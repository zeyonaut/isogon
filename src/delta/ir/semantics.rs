use std::rc::Rc;

use super::syntax::{DynamicTerm, StaticTerm};
use crate::{
	delta::{
		common::{Closure, Copyability, Field, Index, Level, Name, Repr, ReprAtom},
		transform::autolyze::Autolyze,
	},
	utility::rc,
};

#[derive(Clone, Debug)]
pub enum StaticNeutral {
	Variable(Option<Name>, Level),
	Apply(Rc<Self>, Rc<StaticValue>),
	MaxCopyability(Rc<Self>, Rc<Self>),
	ReprUniv(Rc<Self>),
}

#[derive(Clone, Debug)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	CopyabilityType,
	Copyability(Copyability),
	ReprType,
	ReprNone,
	ReprAtom(ReprAtom),
	Lift { ty: DynamicValue, copy: Rc<Self>, repr: Rc<Self> },
	Quote(DynamicValue),
	IndexedProduct(Option<usize>, Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Function(Rc<Closure<Environment, StaticTerm>>),
}

impl From<&Repr> for StaticValue {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(*atom),
		}
	}
}

impl From<Option<&Repr>> for StaticValue {
	fn from(value: Option<&Repr>) -> Self {
		match value {
			Some(repr) => repr.into(),
			None => Self::ReprNone,
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicNeutral {
	Variable(Option<Name>, Level),
	Splice(StaticNeutral),
	// NOTE: The family universe is optional because of conversion-checking with eta-conversion.
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<DynamicValue>,
		fiber_copyability: Option<Rc<StaticValue>>,
		fiber_representation: Option<Rc<StaticValue>>,
		base: Option<Rc<DynamicValue>>,
		family: Option<Rc<Closure<Environment, DynamicTerm>>>,
	},
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe {
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	IndexedProduct {
		grade: Option<usize>,
		base_copyability: Rc<StaticValue>,
		base_representation: Rc<StaticValue>,
		base: Rc<Self>,
		family_copyability: Rc<StaticValue>,
		family_representation: Rc<StaticValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Function {
		base: Rc<Self>,
		family: Rc<Closure<Environment, DynamicTerm>>,
		body: Rc<Closure<Environment, DynamicTerm>>,
	},
}

impl StaticValue {
	pub fn max_copyability(a: Self, b: Self) -> Self {
		use Copyability as C;
		match (a, b) {
			(Self::Copyability(C::Nontrivial), _) => Self::Copyability(C::Nontrivial),
			(Self::Copyability(C::Trivial), b) => b,
			(_, Self::Copyability(C::Nontrivial)) => Self::Copyability(C::Nontrivial),
			(a, Self::Copyability(C::Trivial)) => a,
			(Self::Neutral(a), Self::Neutral(b)) => Self::Neutral(StaticNeutral::MaxCopyability(rc!(a), rc!(b))),
			_ => panic!(),
		}
	}

	pub fn univ_representation(c: Self) -> Self {
		match c {
			StaticValue::Neutral(n) => StaticValue::Neutral(StaticNeutral::ReprUniv(rc!(n))),
			StaticValue::Copyability(Copyability::Trivial) => StaticValue::ReprNone,
			StaticValue::Copyability(Copyability::Nontrivial) => StaticValue::ReprAtom(ReprAtom::Class),
			_ => panic!(),
		}
	}
}

impl From<(Option<Name>, Level)> for StaticValue {
	fn from((name, level): (Option<Name>, Level)) -> Self {
		Self::Neutral(StaticNeutral::Variable(name, level))
	}
}

impl From<(Option<Name>, Level)> for StaticNeutral {
	fn from((name, level): (Option<Name>, Level)) -> Self { Self::Variable(name, level) }
}

impl From<(Option<Name>, Level)> for DynamicValue {
	fn from((name, level): (Option<Name>, Level)) -> Self {
		Self::Neutral(DynamicNeutral::Variable(name, level))
	}
}

impl From<(Option<Name>, Level)> for DynamicNeutral {
	fn from((name, level): (Option<Name>, Level)) -> Self { Self::Variable(name, level) }
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone, Debug)]
pub struct Environment(pub Vec<Value>);

impl Environment {
	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.0.extend(values);
		environment
	}

	pub fn push(&mut self, value: Value) { self.0.push(value); }

	pub fn pop(&mut self) { self.0.pop(); }
}

pub trait Conversion<T> {
	/// Decides whether two values are judgementally equal.
	fn can_convert(self, left: &T, right: &T) -> bool;
}

impl Conversion<StaticValue> for Level {
	fn can_convert(self, left: &StaticValue, right: &StaticValue) -> bool {
		use StaticValue::*;
		match (left, right) {
			(Universe, Universe)
			| (CopyabilityType, CopyabilityType)
			| (ReprType, ReprType)
			| (ReprNone, ReprNone) => true,
			(ReprAtom(left), ReprAtom(right)) => left == right,
			(Lift { ty: left, .. }, Lift { ty: right, .. }) | (Quote(left), Quote(right)) =>
				self.can_convert(left, right),
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),
			(Function(left), Function(right)) =>
				(self + 1).can_convert(&left.autolyze(self), &right.autolyze(self)),
			(Neutral(left), Function(right)) => (self + 1).can_convert(
				&Neutral(StaticNeutral::Apply(rc!(left.clone()), rc!((right.parameter(), self).into()))),
				&right.autolyze(self),
			),
			(Function(left), Neutral(right)) => (self + 1).can_convert(
				&left.autolyze(self),
				&Neutral(StaticNeutral::Apply(rc!(right.clone()), rc!((left.parameter(), self).into()))),
			),
			(
				IndexedProduct(left_grade, left_base, left_family),
				IndexedProduct(right_grade, right_base, right_family),
			) =>
				left_grade == right_grade
					&& self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			(Copyability(left), Copyability(right)) => left == right,
			_ => false,
		}
	}
}

impl Conversion<StaticNeutral> for Level {
	fn can_convert(self, left: &StaticNeutral, right: &StaticNeutral) -> bool {
		use StaticNeutral::*;
		match (left, right) {
			(Variable(_, left), Variable(_, right)) => left == right,
			(MaxCopyability(a_left, b_left), MaxCopyability(a_right, b_right)) =>
				self.can_convert(&**a_left, a_right) && self.can_convert(&**b_left, b_right),
			(ReprUniv(left), ReprUniv(right)) => self.can_convert(&**left, right),
			(Apply(left, left_argument), Apply(right, right_argument)) =>
				self.can_convert(&**left, &right) && self.can_convert(&**left_argument, &right_argument),
			_ => false,
		}
	}
}

impl Conversion<DynamicValue> for Level {
	fn can_convert(self, left: &DynamicValue, right: &DynamicValue) -> bool {
		use DynamicNeutral::*;
		use DynamicValue::*;
		use Field::*;
		match (left, right) {
			(
				Universe { copyability: left_copyability, representation: left_representation },
				Universe { copyability: right_copyability, representation: right_representation },
			) =>
				self.can_convert(&**left_copyability, right_copyability)
					&& self.can_convert(&**left_representation, right_representation),
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),
			(Function { body: left, .. }, Function { body: right, .. }) =>
				(self + 1).can_convert(&left.autolyze(self), &right.autolyze(self)),
			(Neutral(left), Function { body: right, .. }) => (self + 1).can_convert(
				&Neutral(Apply {
					scrutinee: rc!(left.clone()),
					argument: rc!((right.parameter(), self).into()),
					fiber_copyability: None,
					fiber_representation: None,
					base: None,
					family: None,
				}),
				&right.autolyze(self),
			),
			(Function { body: left, .. }, Neutral(right)) => (self + 1).can_convert(
				&left.autolyze(self),
				&Neutral(Apply {
					scrutinee: rc!(right.clone()),
					argument: rc!((left.parameter(), self).into()),
					fiber_copyability: None,
					fiber_representation: None,
					base: None,
					family: None,
				}),
			),
			// NOTE: Annotation conversion not implemented, as it's unclear if it gives any useful advantages.
			(
				IndexedProduct { base: left_base, family: left_family, .. },
				IndexedProduct { base: right_base, family: right_family, .. },
			) =>
				self.can_convert(&**left_base, &right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			_ => false,
		}
	}
}

impl Conversion<DynamicNeutral> for Level {
	fn can_convert(self, left: &DynamicNeutral, right: &DynamicNeutral) -> bool {
		use DynamicNeutral::*;
		match (left, right) {
			(Variable(_, left), Variable(_, right)) => left == right,
			(
				Apply { scrutinee: left, argument: left_argument, .. },
				Apply { scrutinee: right, argument: right_argument, .. },
			) => self.can_convert(&**left, right) && self.can_convert(&**left_argument, right_argument),
			(Splice(left), Splice(right)) => self.can_convert(left, right),
			_ => false,
		}
	}
}
