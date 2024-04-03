use std::rc::Rc;

use super::syntax::{DynamicTerm, StaticTerm};
use crate::{
	delta::common::{Closure, Cpy, Field, Index, Level, Name, Repr, ReprAtom},
	utility::rc,
};

#[derive(Clone, Debug)]
pub struct KindValue {
	pub copy: StaticValue,
	pub repr: StaticValue,
}

impl KindValue {
	pub const fn path() -> Self { Self { copy: StaticValue::CpyValue(Cpy::Tr), repr: StaticValue::ReprNone } }

	pub const fn fun() -> Self {
		Self { copy: StaticValue::CpyValue(Cpy::Nt), repr: StaticValue::ReprAtom(ReprAtom::Fun) }
	}

	pub const fn enu() -> Self {
		Self { copy: StaticValue::CpyValue(Cpy::Tr), repr: StaticValue::ReprAtom(ReprAtom::Byte) }
	}

	pub const fn ty() -> Self { Self { copy: StaticValue::CpyValue(Cpy::Tr), repr: StaticValue::ReprNone } }

	// TODO: Only consider nat to be trivial for slightly simpler implementation.
	pub const fn nat() -> Self {
		Self { copy: StaticValue::CpyValue(Cpy::Tr), repr: StaticValue::ReprAtom(ReprAtom::Nat) }
	}

	pub const fn ptr() -> Self {
		Self { copy: StaticValue::CpyValue(Cpy::Nt), repr: StaticValue::ReprAtom(ReprAtom::Ptr) }
	}

	pub fn wrap(self) -> Self { Self { copy: StaticValue::CpyValue(Cpy::Nt), repr: self.repr } }

	pub fn exp(self, grade: usize) -> Self {
		Self { copy: self.copy, repr: StaticValue::ReprExp(grade, self.repr.into()) }
	}

	pub fn pair(a: Self, b: Self) -> Self {
		Self {
			copy: StaticValue::max_copyability(a.copy, b.copy),
			repr: StaticValue::pair_representation(a.repr, b.repr),
		}
	}
}

#[derive(Clone, Debug)]
pub enum StaticValue {
	// Neutrals.
	Neutral(StaticNeutral),

	// Types and universe indices.
	Universe(Cpy),

	Cpy,
	CpyValue(Cpy),

	ReprType,
	ReprNone,
	ReprAtom(ReprAtom),
	ReprExp(usize, Rc<Self>),
	// NOTE: This is a little type-unsafe in exchange for less redundant code; we need to make sure that these two never contain a ReprNone.
	ReprPair(Rc<Self>, Rc<Self>),

	// Quoted programs.
	Lift {
		ty: DynamicValue,
		kind: Rc<KindValue>,
	},
	Quote(DynamicValue),

	// Repeated programs.
	Exp(usize, Rc<Self>),
	Repeat(usize, Rc<Self>),

	// Dependent functions.
	IndexedProduct {
		grade: usize,
		base_copy: Cpy,
		base: Rc<Self>,
		family: Rc<Closure<Environment, StaticTerm>>,
	},
	Function(usize, Rc<Closure<Environment, StaticTerm>>),

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
	Num(usize),
}

#[derive(Clone, Debug)]
pub enum StaticNeutral {
	// Variables.
	Variable(Option<Name>, Level),

	// Hacks.
	CpyMax(Rc<Self>, Rc<Self>),

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

impl From<&Repr> for StaticValue {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(*atom),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Exp(n, r) => Self::ReprExp(*n, Self::from(&**r).into()),
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
pub enum DynamicValue {
	// Neutrals.
	Neutral(DynamicNeutral),

	// Types.
	Universe {
		kind: Rc<KindValue>,
	},

	// Repeated programs.
	Exp(usize, Rc<Self>),
	Repeat(usize, Rc<Self>),

	// Dependent functions.
	IndexedProduct {
		grade: usize,
		base_kind: Rc<KindValue>,
		base: Rc<Self>,
		family_kind: Rc<KindValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Function {
		grade: usize,
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
	Num(usize),

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

impl StaticValue {
	pub fn max_copyability(a: Self, b: Self) -> Self {
		use Cpy as C;
		match (a, b) {
			(Self::CpyValue(C::Nt), _) => Self::CpyValue(C::Nt),
			(Self::CpyValue(C::Tr), b) => b,
			(_, Self::CpyValue(C::Nt)) => Self::CpyValue(C::Nt),
			(a, Self::CpyValue(C::Tr)) => a,
			(Self::Neutral(a), Self::Neutral(b)) => Self::Neutral(StaticNeutral::CpyMax(rc!(a), rc!(b))),
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
