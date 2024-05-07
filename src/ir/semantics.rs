use std::rc::Rc;

use super::syntax::{DynamicTerm, StaticTerm};
use crate::{
	common::{ArraySize, Closure, Cost, Cpy, Field, Fragment, Index, Level, Name, Repr, ReprAtom},
	frontend::conversion::Conversion,
};

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone, Debug)]
pub enum StaticValue {
	// Neutrals.
	Neutral(StaticNeutral),

	// Types and universe indices.
	Universe(Cpy),

	Cpy,
	CpyValue(CpyValue),

	ReprType,
	ReprNone,
	ReprAtom(ReprAtom),
	ReprExp(ArraySize, Rc<KindValue>),
	// NOTE: This is a little type-unsafe in exchange for less redundant code; we need to make sure that these two never contain a ReprNone.
	ReprPair(Rc<Self>, Rc<Self>),

	// Quoted programs.
	Lift {
		ty: DynamicValue,
		kind: Rc<KindValue>,
	},
	Quote(DynamicValue),

	// Repeated programs.
	Exp(Cost, Cpy, Rc<Self>),
	Promote(Cost, Rc<Self>),

	// Dependent functions.
	IndexedProduct {
		fragment: Fragment,
		base_copy: Cpy,
		base: Rc<Self>,
		family_copy: Cpy,
		family: Rc<Closure<Environment, StaticTerm>>,
	},
	Function(Fragment, Rc<Closure<Environment, StaticTerm>>),

	// Dependent pairs.
	IndexedSum {
		base_copy: Cpy,
		base: Rc<Self>,
		family_copy: Cpy,
		family: Rc<Closure<Environment, StaticTerm>>,
	},
	Pair(Rc<Self>, Rc<Self>),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),

	// Natural numbers.
	Nat,
	Num(u64),
}

#[derive(Clone, Debug)]
pub enum StaticNeutral {
	// Variables.
	Variable(Option<Name>, Level),

	// Repeated programs.
	ExpProject(Rc<Self>),

	// Dependent functions.
	Apply(Rc<Self>, Rc<StaticValue>),

	// Dependent pairs.
	Project(Rc<Self>, Field),

	// Enumerated numbers.
	CaseEnum {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		cases: Vec<StaticValue>,
	},

	// Natural numbers.
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		case_nil: Rc<StaticValue>,
		case_suc: Rc<Closure<Environment, StaticTerm, 2>>,
	},
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	// Neutrals.
	Neutral(DynamicNeutral),

	// Types.
	Universe {
		kind: Rc<KindValue>,
	},

	// Repeated programs.
	Exp(u64, Rc<KindValue>, Rc<Self>),
	Promote(u64, Rc<Self>),

	// Dependent functions.
	IndexedProduct {
		fragment: Fragment,
		base_kind: Rc<KindValue>,
		base: Rc<Self>,
		family_kind: Rc<KindValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Function {
		fragment: Fragment,
		body: Rc<Closure<Environment, DynamicTerm>>,
	},

	// Dependent pairs.
	IndexedSum {
		base_kind: Rc<KindValue>,
		base: Rc<Self>,
		family_kind: Rc<KindValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Pair(Rc<Self>, Rc<Self>),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),

	// Paths.
	Id {
		kind: Rc<KindValue>,
		space: Rc<Self>,
		left: Rc<Self>,
		right: Rc<Self>,
	},
	Refl,

	// Natural numbers.
	Nat,
	Num(u64),

	// Wrappers.
	Bx {
		kind: Rc<KindValue>,
		inner: Rc<Self>,
	},
	BxValue(Rc<Self>),
	Wrap {
		kind: Rc<KindValue>,
		inner: Rc<Self>,
	},
	WrapValue(Rc<Self>),
}

#[derive(Clone, Debug)]
pub enum DynamicNeutral {
	// Variables.
	Variable(Option<Name>, Level),

	// Quoted programs.
	Splice(StaticNeutral),

	// Repeated programs.
	ExpProject(Rc<Self>),

	// Dependent functions.
	// NOTE: The family universe is optional because of conversion-checking with eta-conversion.
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<DynamicValue>,
	},

	// Dependent pairs.
	Project {
		scrutinee: Rc<Self>,
		projection: Field,
	},

	// Enumerated numbers.
	CaseEnum {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
		cases: Vec<DynamicValue>,
	},

	// Paths.
	CasePath {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, DynamicTerm, 2>>,
		case_refl: Rc<DynamicValue>,
	},

	// Natural numbers.
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		case_nil: Rc<DynamicValue>,
		case_suc: Rc<Closure<Environment, DynamicTerm, 2>>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
	},

	// Wrappers.
	BxProject(Rc<Self>),
	WrapProject(Rc<Self>),
}

#[derive(Clone, Debug)]
pub struct KindValue {
	pub copy: StaticValue,
	pub repr: StaticValue,
}

#[derive(Clone, Debug)]
pub struct Environment(pub Vec<Value>);

#[derive(Clone, Debug)]
pub enum CpyValue {
	Nt,
	Max(Vec<StaticNeutral>),
}

impl StaticValue {
	pub const fn cpy(value: Cpy) -> Self {
		match value {
			Cpy::Nt => Self::CpyValue(CpyValue::Nt),
			Cpy::Tr => Self::CpyValue(CpyValue::Max(Vec::new())),
		}
	}

	pub fn is_trivial(&self) -> bool {
		matches!(self, StaticValue::CpyValue(CpyValue::Max(v)) if v.is_empty())
	}

	fn combine_max_copyability(
		level: Level,
		mut a_set: Vec<StaticNeutral>,
		b_set: Vec<StaticNeutral>,
	) -> Self {
		let len = a_set.len();
		'b: for b in b_set {
			'a: for a in &a_set[0..len] {
				if level.can_convert(a, &b) {
					continue 'b;
				} else {
					continue 'a;
				}
			}
			a_set.push(b);
		}
		Self::CpyValue(CpyValue::Max(a_set))
	}

	pub fn max_copyability(level: Level, a: Self, b: Self) -> Self {
		use CpyValue as C;
		match (a, b) {
			(Self::CpyValue(C::Nt), _) => Self::CpyValue(C::Nt),
			(_, Self::CpyValue(C::Nt)) => Self::CpyValue(C::Nt),
			(Self::Neutral(a), Self::Neutral(b)) => Self::combine_max_copyability(level, vec![a], vec![b]),
			(Self::Neutral(a), Self::CpyValue(C::Max(b_set))) =>
				Self::combine_max_copyability(level, vec![a], b_set),
			(Self::CpyValue(C::Max(a_set)), Self::Neutral(b)) =>
				Self::combine_max_copyability(level, a_set, vec![b]),
			(Self::CpyValue(C::Max(a_set)), Self::CpyValue(C::Max(b_set))) =>
				Self::combine_max_copyability(level, a_set, b_set),
			_ => panic!(),
		}
	}

	pub fn pair_representation(a: Self, b: Self) -> Self {
		match (a, b) {
			(Self::ReprNone, b) => b,
			(a, Self::ReprNone) => a,
			(a, b) => Self::ReprPair(a.into(), b.into()),
		}
	}

	pub fn exp_representation(len: ArraySize, kind: KindValue) -> Self {
		match kind.copy {
			StaticValue::CpyValue(CpyValue::Max(cpys)) if cpys.is_empty() => kind.repr,
			StaticValue::Neutral(_) | StaticValue::CpyValue(_) => match kind.repr {
				StaticValue::ReprNone => StaticValue::ReprNone,
				_ => StaticValue::ReprExp(len, kind.into()),
			},
			_ => panic!(),
		}
	}

	pub fn field(self, field: Field) -> Self {
		match self {
			StaticValue::Pair(basepoint, fiberpoint) => match field {
				Field::Base => basepoint.as_ref().clone(),
				Field::Fiber => fiberpoint.as_ref().clone(),
			},
			StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Project(neutral.into(), field)),
			_ => panic!(),
		}
	}

	pub fn suc(self) -> Self {
		match self {
			StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Suc(neutral.into())),
			StaticValue::Num(n) => StaticValue::Num(n + 1),
			_ => panic!(),
		}
	}

	pub fn exp_project(self) -> Self {
		match self {
			StaticValue::Promote(_, v) => v.as_ref().clone(),
			StaticValue::Neutral(n) => StaticValue::Neutral(StaticNeutral::ExpProject(n.into())),
			_ => panic!(),
		}
	}
}

impl DynamicValue {
	pub fn field(self, field: Field) -> Self {
		match self {
			DynamicValue::Pair(basepoint, fiberpoint) => match field {
				Field::Base => basepoint.as_ref().clone(),
				Field::Fiber => fiberpoint.as_ref().clone(),
			},
			DynamicValue::Neutral(neutral) =>
				DynamicValue::Neutral(DynamicNeutral::Project { scrutinee: neutral.into(), projection: field }),
			_ => panic!(),
		}
	}

	pub fn suc(self) -> Self {
		match self {
			DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Suc(neutral.into())),
			DynamicValue::Num(n) => DynamicValue::Num(n + 1),
			_ => panic!(),
		}
	}

	pub fn exp_project(self) -> Self {
		match self {
			DynamicValue::Promote(_, v) => v.as_ref().clone(),
			DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::ExpProject(n.into())),
			_ => panic!(),
		}
	}
}

impl From<Cpy> for StaticValue {
	fn from(value: Cpy) -> Self { Self::cpy(value) }
}

impl From<&Repr> for StaticValue {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(*atom),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Array(n, r) => Self::ReprExp(
				*n,
				KindValue { copy: StaticValue::CpyValue(CpyValue::Nt), repr: Self::from(&**r) }.into(),
			),
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

impl KindValue {
	pub const fn path() -> Self { Self { copy: StaticValue::cpy(Cpy::Tr), repr: StaticValue::ReprNone } }

	pub const fn fun() -> Self {
		Self { copy: StaticValue::cpy(Cpy::Nt), repr: StaticValue::ReprAtom(ReprAtom::Fun) }
	}

	pub const fn enu() -> Self {
		Self { copy: StaticValue::cpy(Cpy::Tr), repr: StaticValue::ReprAtom(ReprAtom::Byte) }
	}

	pub const fn ty() -> Self { Self { copy: StaticValue::cpy(Cpy::Tr), repr: StaticValue::ReprNone } }

	// NOTE: Only consider nat to be trivial for slightly simpler implementation.
	pub const fn nat() -> Self {
		Self { copy: StaticValue::cpy(Cpy::Tr), repr: StaticValue::ReprAtom(ReprAtom::Nat) }
	}

	pub const fn ptr() -> Self {
		Self { copy: StaticValue::cpy(Cpy::Nt), repr: StaticValue::ReprAtom(ReprAtom::Ptr) }
	}

	pub fn wrap(self) -> Self { Self { copy: Cpy::Nt.into(), repr: self.repr } }

	pub fn exp(self, grade: u64) -> Self {
		Self {
			repr: match grade {
				0 => StaticValue::ReprNone,
				1 => self.repr,
				grade => StaticValue::exp_representation(ArraySize(grade), self.clone()),
			},
			copy: if grade == 0 { StaticValue::cpy(Cpy::Tr) } else { self.copy },
		}
	}

	pub fn pair(level: Level, a: Self, b: Self) -> Self {
		Self {
			copy: StaticValue::max_copyability(level, a.copy, b.copy),
			repr: StaticValue::pair_representation(a.repr, b.repr),
		}
	}
}

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

	pub fn level(&self) -> Level { Level(self.0.len()) }

	pub fn push(&mut self, value: Value) { self.0.push(value); }

	pub fn pop(&mut self) { self.0.pop(); }
}
