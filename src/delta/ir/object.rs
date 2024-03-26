use std::{fmt::Debug, rc::Rc};

use super::syntax::{DynamicTerm, StaticTerm};
use crate::delta::common::{Closure, Copyability, Field, Index, Level, Name, Repr, UniverseKind};

#[derive(Clone)]
pub enum StaticValue {
	Type,
	Quote(Rc<DynamicValue>),
	Function(Closure<Environment, StaticTerm>),
	Pair(Rc<Self>, Rc<Self>),
	Num(usize),
	EnumValue(u8),
	Copyability(Copyability),
	Repr(Option<Repr>),
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
	Variable(Option<Name>, Level),
	Let {
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Closure<Environment, DynamicTerm>,
	},
	Universe(UniverseKind),
	Pi {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Closure<Environment, DynamicTerm>,
	},
	Function {
		// TODO: This is kind of redundant, since binders store parameter names and arity,
		// and family and body should have the same of both; the single parameter is also
		// associated with the base. Is it possible to have a more generic binder type that
		// can accommodate this extra data, but without significantly affecting existing binder code?
		base: Rc<Self>,
		family: Closure<Environment, DynamicTerm>,
		body: Closure<Environment, DynamicTerm>,
	},
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<Self>,
		fiber_universe: UniverseKind,
		base: Rc<Self>,
		family: Closure<Environment, DynamicTerm>,
	},
	Sigma {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Closure<Environment, DynamicTerm>,
	},
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	// TODO: Is this enough information? We might want more information for fiber projections (e.g. the repr of the base.)
	Project(Rc<Self>, Field, UniverseKind),
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		case_nil: Rc<Self>,
		case_suc: Closure<Environment, DynamicTerm, 2>,
		fiber_universe: UniverseKind,
		motive: Closure<Environment, DynamicTerm>,
	},
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Rc<Self>,
		cases: Vec<Self>,
		fiber_universe: UniverseKind,
		motive: Closure<Environment, DynamicTerm>,
	},
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
	WrapType(Rc<Self>, UniverseKind),
	WrapNew(Rc<Self>),
	Unwrap(Rc<Self>, UniverseKind),
	RcType(Rc<Self>, UniverseKind),
	RcNew(Rc<Self>),
	UnRc(Rc<Self>, UniverseKind),
}
