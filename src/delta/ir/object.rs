use std::{fmt::Debug, rc::Rc};

use super::syntax::{DynamicTerm, StaticTerm};
use crate::delta::common::{Closure, Cpy, Field, Index, Level, Name, Repr, UniverseKind};

#[derive(Clone)]
pub enum StaticValue {
	// Types and universe indices.
	Type,
	CpyValue(Cpy),
	ReprValue(Option<Repr>),

	// Quoted programs.
	Quote(Rc<DynamicValue>),

	// Dependent functions.
	Function(Closure<Environment, StaticTerm>),

	// Dependent pairs.
	Pair(Rc<Self>, Rc<Self>),

	// Enumerated numbers.
	EnumValue(u8),

	// Natural numbers.
	NatValue(usize),
}

impl Debug for StaticValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Type => write!(f, "Type"),
			Self::Quote(quotee) => f.debug_tuple("Quote").field(quotee).finish(),
			Self::Function(_) => f.debug_tuple("Function").field(&format_args!("_")).finish(),
			_ => write!(f, "<...>"),
		}
	}
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone, Debug)]
pub struct Environment {
	values: Vec<Value>,
}

impl Environment {
	pub const fn new() -> Self { Self { values: Vec::new() } }

	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.values.extend(values);
		environment
	}
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	// Variables.
	Variable(Option<Name>, Level),

	// Let-expressions.
	Let {
		grade: usize,
		ty_kind: UniverseKind,
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Closure<Environment, DynamicTerm>,
	},

	// Types.
	Universe(UniverseKind),

	// Repeated programs.

	// Dependent functions.
	Pi {
		grade: usize,
		base_kind: UniverseKind,
		base: Rc<Self>,
		family_kind: UniverseKind,
		family: Closure<Environment, DynamicTerm>,
	},
	Function {
		grade: usize,
		body: Closure<Environment, DynamicTerm>,
		domain_kind: Option<UniverseKind>,
		codomain_kind: Option<UniverseKind>,
	},
	Apply {
		scrutinee: Rc<Self>,
		grade: Option<usize>,
		argument: Rc<Self>,
		family_kind: Option<UniverseKind>,
	},

	// Dependent pairs.
	Sg {
		base_kind: UniverseKind,
		base: Rc<Self>,
		family_kind: UniverseKind,
		family: Closure<Environment, DynamicTerm>,
	},
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	SgLet {
		grade: usize,
		argument: Box<Self>,
		kinds: [UniverseKind; 2],
		tail: Closure<Environment, DynamicTerm, 2>,
	},
	SgField(Rc<Self>, Field),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Rc<Self>,
		motive_kind: Option<UniverseKind>,
		motive: Closure<Environment, DynamicTerm>,
		cases: Vec<Self>,
	},

	// Paths.
	Id {
		kind: UniverseKind,
		space: Rc<Self>,
		left: Rc<Self>,
		right: Rc<Self>,
	},
	Refl,
	CasePath {
		scrutinee: Rc<Self>,
		motive: Closure<Environment, DynamicTerm, 2>,
		case_refl: Rc<Self>,
	},

	// Natural numbers.
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive_kind: Option<UniverseKind>,
		motive: Closure<Environment, DynamicTerm>,
		case_nil: Rc<Self>,
		case_suc: Closure<Environment, DynamicTerm, 2>,
	},

	// Wrappers.
	Bx(Rc<Self>, UniverseKind),
	BxValue(Rc<Self>),
	BxProject(Rc<Self>, Option<UniverseKind>),

	Wrap(Rc<Self>, UniverseKind),
	WrapValue(Rc<Self>),
	WrapProject(Rc<Self>, Option<UniverseKind>),
}
