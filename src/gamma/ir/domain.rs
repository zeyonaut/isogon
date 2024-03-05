use std::rc::Rc;

use super::syntax::{DynamicTerm, StaticTerm};
use crate::{
	gamma::{
		common::{Closure, Copyability, Field, Index, Level, Name, Repr, ReprAtom},
		transform::evaluate::Autolyze,
	},
	utility::rc,
};

#[derive(Clone, Debug)]
pub enum StaticNeutral {
	Variable(Option<Name>, Level),
	Apply(Rc<Self>, Rc<StaticValue>),
	Project(Rc<Self>, Field),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		case_nil: Rc<StaticValue>,
		case_suc: Rc<Closure<Environment, StaticTerm, 2>>,
	},
	Suc(Rc<Self>),
	CaseEnum {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		cases: Vec<StaticValue>,
	},
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
	// NOTE: This is a little type-unsafe in exchange for less redundant code; we need to make sure that these two never contain a ReprNone.
	ReprPair(Rc<Self>, Rc<Self>),
	ReprMax(Rc<Self>, Rc<Self>),
	Lift { ty: DynamicValue, copy: Rc<Self>, repr: Rc<Self> },
	Quote(DynamicValue),
	IndexedProduct(Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Function(Rc<Closure<Environment, StaticTerm>>),
	IndexedSum(Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
	Enum(u16),
	EnumValue(u16, u8),
}

impl From<&Repr> for StaticValue {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(*atom),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Max(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
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
	// NOTE: The universe is optional because of conversion-checking with eta-conversion.
	Project {
		scrutinee: Rc<Self>,
		projection: Field,
		copyability: Option<Rc<StaticValue>>,
		representation: Option<Rc<StaticValue>>,
	},
	CaseNat {
		scrutinee: Rc<Self>,
		case_nil: Rc<DynamicValue>,
		case_suc: Rc<Closure<Environment, DynamicTerm, 2>>,
		fiber_copyability: Rc<StaticValue>,
		fiber_representation: Rc<StaticValue>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
	},
	Suc(Rc<Self>),
	CaseEnum {
		scrutinee: Rc<Self>,
		cases: Vec<DynamicValue>,
		fiber_copyability: Rc<StaticValue>,
		fiber_representation: Rc<StaticValue>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
	},
	Unwrap {
		scrutinee: Rc<Self>,
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	UnRc {
		scrutinee: Rc<Self>,
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
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
	IndexedSum {
		base_copyability: Rc<StaticValue>,
		base_representation: Rc<StaticValue>,
		base: Rc<Self>,
		family_copyability: Rc<StaticValue>,
		family_representation: Rc<StaticValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
	Enum(u16),
	EnumValue(u16, u8),
	WrapType {
		inner: Rc<Self>,
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	WrapNew(Rc<Self>),
	RcType {
		inner: Rc<Self>,
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	RcNew(Rc<Self>),
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

	pub fn pair_representation(a: Self, b: Self) -> Self {
		match (a, b) {
			(Self::ReprNone, b) => b,
			(a, Self::ReprNone) => a,
			(a, b) => Self::ReprPair(rc!(a), rc!(b)),
		}
	}

	pub fn max_representation(a: Self, b: Self) -> Self {
		match (a, b) {
			(Self::ReprNone, b) => b,
			(a, Self::ReprNone) => a,
			(a, b) => Self::ReprMax(rc!(a), rc!(b)),
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

impl From<(Option<Name>, Level)> for DynamicValue {
	fn from((name, level): (Option<Name>, Level)) -> Self {
		Self::Neutral(DynamicNeutral::Variable(name, level))
	}
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

	pub fn push(&mut self, value: Value) {
		self.0.push(value);
	}
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
			| (Nat, Nat)
			| (CopyabilityType, CopyabilityType)
			| (ReprType, ReprType)
			| (ReprNone, ReprNone) => true,
			(Enum(left), Enum(right)) => left == right,
			(ReprAtom(left), ReprAtom(right)) => left == right,
			(ReprPair(left0, left1), ReprPair(right0, right1)) =>
				self.can_convert(&**left0, right0) && self.can_convert(&**left1, right1),
			(ReprMax(left0, left1), ReprMax(right0, right1)) =>
				self.can_convert(&**left0, right0) && self.can_convert(&**left1, right1),
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
			(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, &right_bp) && self.can_convert(&**left_fp, &right_fp),
			(IndexedProduct(left_base, left_family), IndexedProduct(right_base, right_family))
			| (IndexedSum(left_base, left_family), IndexedSum(right_base, right_family)) =>
				self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			(Num(left), Num(right)) => left == right,
			(EnumValue(_, left), EnumValue(_, right)) => left == right,
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
			(Project(left, left_projection), Project(right, right_projection)) =>
				left_projection == right_projection && self.can_convert(&**left, right),
			(
				CaseNat { scrutinee: l_scrutinee, motive: l_motive, case_nil: l_case_nil, case_suc: l_case_suc },
				CaseNat { scrutinee: r_scrutinee, motive: r_motive, case_nil: r_case_nil, case_suc: r_case_suc },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.autolyze(self), &r_motive.autolyze(self))
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.autolyze(self), &r_case_suc.autolyze(self)),
			(
				CaseEnum { scrutinee: l_scrutinee, cases: l_cases, .. },
				CaseEnum { scrutinee: r_scrutinee, cases: r_cases, .. },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& l_cases
						.iter()
						.zip(r_cases.iter())
						.fold(true, |acc, (left, right)| acc && self.can_convert(left, right)),
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
			(WrapType { inner: left, .. }, WrapType { inner: right, .. })
			| (WrapNew(left), WrapNew(right))
			| (RcType { inner: left, .. }, RcType { inner: right, .. })
			| (RcNew(left), RcNew(right)) => self.can_convert(&**left, right),
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
			(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, &right_bp) && self.can_convert(&**left_fp, &right_fp),
			(Neutral(left), Pair(right_bp, right_fp)) =>
				self.can_convert(
					&Neutral(Project {
						scrutinee: left.clone().into(),
						projection: Base,
						copyability: None,
						representation: None,
					}),
					&right_bp,
				) && self.can_convert(
					&Neutral(Project {
						scrutinee: left.clone().into(),
						projection: Fiber,
						copyability: None,
						representation: None,
					}),
					&right_fp,
				),
			(Pair(left_bp, left_fp), Neutral(right)) =>
				self.can_convert(
					&**left_bp,
					&Neutral(Project {
						scrutinee: right.clone().into(),
						projection: Base,
						copyability: None,
						representation: None,
					}),
				) && self.can_convert(
					&**left_fp,
					&Neutral(Project {
						scrutinee: right.clone().into(),
						projection: Fiber,
						copyability: None,
						representation: None,
					}),
				),
			// NOTE: Annotation conversion not implemented, as it's unclear if it gives any useful advantages.
			(
				IndexedProduct { base: left_base, family: left_family, .. },
				IndexedProduct { base: right_base, family: right_family, .. },
			)
			| (
				IndexedSum { base: left_base, family: left_family, .. },
				IndexedSum { base: right_base, family: right_family, .. },
			) =>
				self.can_convert(&**left_base, &right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			(Nat, Nat) => true,
			(Enum(left), Enum(right)) => left == right,
			(Num(left), Num(right)) => left == right,
			(EnumValue(_, left), EnumValue(_, right)) => left == right,
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
			(
				Project { scrutinee: left, projection: left_projection, .. },
				Project { scrutinee: right, projection: right_projection, .. },
			) => left_projection == right_projection && self.can_convert(&**left, right),
			(Unwrap { scrutinee: left, .. }, Unwrap { scrutinee: right, .. })
			| (UnRc { scrutinee: left, .. }, UnRc { scrutinee: right, .. })
			| (Suc(left), Suc(right)) => self.can_convert(&**left, right),
			(Splice(left), Splice(right)) => self.can_convert(left, right),
			(
				CaseNat { scrutinee: l_scrutinee, case_nil: l_case_nil, case_suc: l_case_suc, .. },
				CaseNat { scrutinee: r_scrutinee, case_nil: r_case_nil, case_suc: r_case_suc, .. },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.autolyze(self), &r_case_suc.autolyze(self)),
			(
				CaseEnum { scrutinee: l_scrutinee, cases: l_cases, .. },
				CaseEnum { scrutinee: r_scrutinee, cases: r_cases, .. },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& l_cases
						.iter()
						.zip(r_cases.iter())
						.fold(true, |acc, (left, right)| acc && self.can_convert(left, right)),
			_ => false,
		}
	}
}
