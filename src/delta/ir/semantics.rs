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
	LetExp { scrutinee: Rc<Self>, grade: usize, tail: Rc<Closure<Environment, StaticTerm>>,},
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
	ReprExp(usize, Rc<Self>),

	Lift { ty: DynamicValue, copy: Rc<Self>, repr: Rc<Self> },
	Quote(DynamicValue),
	IndexedProduct(usize, Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Function(usize, Rc<Closure<Environment, StaticTerm>>),
	
	Exp(usize, Rc<Self>),
	Repeat(usize, Rc<Self>),
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
	LetExp { scrutinee: Rc<Self>, grade: usize, tail: Rc<Closure<Environment, DynamicTerm>>,},
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe {
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	IndexedProduct {
		grade: usize,
		base_copyability: Rc<StaticValue>,
		base_representation: Rc<StaticValue>,
		base: Rc<Self>,
		family_copyability: Rc<StaticValue>,
		family_representation: Rc<StaticValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Function {
		grade: usize,
		base: Rc<Self>,
		family: Rc<Closure<Environment, DynamicTerm>>,
		body: Rc<Closure<Environment, DynamicTerm>>,
	},
	Exp(usize, Rc<Self>),
	Repeat(usize, Rc<Self>),
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

			(Exp(grade_l, ty_l), Exp(grade_r, ty_r)) => grade_l == grade_r && self.can_convert(&**ty_l, ty_r),
			(Repeat(_, left), Repeat(_, right)) => self.can_convert(&**left, right),

			(Neutral(left), Neutral(right)) => self.can_convert(left, right),
			(Function(_, left), Function(_, right)) =>
				(self + 1).can_convert(&left.autolyze(self), &right.autolyze(self)),
			(Neutral(left), Function(_, right)) => (self + 1).can_convert(
				&Neutral(StaticNeutral::Apply(rc!(left.clone()), rc!((right.parameter(), self).into()))),
				&right.autolyze(self),
			),
			(Function(_, left), Neutral(right)) => (self + 1).can_convert(
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
			(Apply(left, left_argument), Apply(right, right_argument)) =>
				self.can_convert(&**left, &right) && self.can_convert(&**left_argument, &right_argument),
			(LetExp { scrutinee: sl, grade: gl, tail: tl }, LetExp { scrutinee: sr, grade: gr, tail: tr }) => self.can_convert(&**sl, sr) && gl == gr && self.can_convert(&tl.autolyze(self), &tr.autolyze(self)),
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
			// Neutrals.
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),

			// Universes.
			(
				Universe { copyability: left_copyability, representation: left_representation },
				Universe { copyability: right_copyability, representation: right_representation },
			) =>
				self.can_convert(&**left_copyability, right_copyability)
					&& self.can_convert(&**left_representation, right_representation),

			// Exponentials.
			(Exp(grade_l, ty_l), Exp(grade_r, ty_r)) => grade_l == grade_r && self.can_convert(&**ty_l, ty_r),
			(Repeat(_, left), Repeat(_, right)) => self.can_convert(&**left, right),

			// Functions.			
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
			// Variables.
			(Variable(_, left), Variable(_, right)) => left == right,
			
			// Exponential unpacking.
			(LetExp { scrutinee: sl, grade: gl, tail: tl }, LetExp { scrutinee: sr, grade: gr, tail: tr }) => self.can_convert(&**sl, sr) && gl == gr && self.can_convert(&tl.autolyze(self), &tr.autolyze(self)),

			// Function application.
			(
				Apply { scrutinee: left, argument: left_argument, .. },
				Apply { scrutinee: right, argument: right_argument, .. },
			) => self.can_convert(&**left, right) && self.can_convert(&**left_argument, right_argument),

			// Metaprogram splicing.
			(Splice(left), Splice(right)) => self.can_convert(left, right),
			_ => false,
		}
	}
}
