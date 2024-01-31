use std::{fmt::Debug, rc::Rc};

use super::syntax::StaticTerm;
use crate::gamma::common::{
	Binder, Closure, Copyability, Index, Level, Name, Projection, Repr, UniverseKind,
};

#[derive(Clone)]
pub enum Metavalue {
	Type,
	Quote(Rc<Obterm>),
	Function(Closure<Environment, StaticTerm>),
	Pair(Rc<Self>, Rc<Self>),
	Num(usize),
	BoolValue(bool),
	Copyability(Copyability),
	Repr(Option<Repr>),
}

impl Debug for Metavalue {
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
	Static(Metavalue),
	Dynamic(Name, Level),
}

#[derive(Clone, Debug)]
pub struct Environment {
	values: Vec<Value>,
	dynamic_context_length: Level,
}

impl Environment {
	pub fn new() -> Self {
		Self { values: Vec::new(), dynamic_context_length: Level(0) }
	}

	pub fn lookup_static(&self, Index(i): Index) -> Metavalue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> Obterm {
		let Some(Value::Dynamic(name, level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		Obterm::Variable(*name, *level)
	}

	#[must_use]
	pub fn bind<const N: usize>(&self, names: [Name; N]) -> Self {
		let mut environment = self.clone();
		for name in names {
			environment.values.push(Value::Dynamic(name, environment.dynamic_context_length));
			environment.dynamic_context_length += 1;
		}
		environment
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.values.extend(values);
		environment
	}
}

#[derive(Clone, Debug)]
pub enum Obterm {
	Variable(Name, Level),
	Let {
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Binder<Rc<Self>>,
	},
	Universe(UniverseKind),
	Pi {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Binder<Rc<Self>>,
	},
	Function {
		// TODO: This is kind of redundant, since binders store parameter names and arity,
		// and family and body should have the same of both; the single parameter is also
		// associated with the base. Is it possible to have a more generic binder type that
		// can accommodate this extra data, but without significantly affecting existing binder code?
		base: Rc<Self>,
		family: Binder<Rc<Self>>,
		body: Binder<Rc<Self>>,
	},
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<Self>,
	},
	Sigma {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Binder<Rc<Self>>,
	},
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	Project(Rc<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_nil: Rc<Self>,
		case_suc: Binder<Rc<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_false: Rc<Self>,
		case_true: Rc<Self>,
	},
	WrapType(Rc<Self>),
	WrapNew(Rc<Self>),
	Unwrap(Rc<Self>),
	RcType(Rc<Self>),
	RcNew(Rc<Self>),
	UnRc(Rc<Self>),
}

impl Obterm {
	// Yields the characteristic of the subset of all levels < level that occur as a variable in a value.
	pub fn occurences(&self, Level(level): Level) -> Vec<bool> {
		fn mark_occurrents(value: &Obterm, is_occurrent: &mut Vec<bool>) {
			match value {
				Obterm::Variable(_, Level(l)) =>
					if let Some(l_is_occurrent) = is_occurrent.get_mut(*l) {
						*l_is_occurrent = true;
					},

				// Cases with binders.
				Obterm::Function { base, family, body } => {
					mark_occurrents(base, is_occurrent);
					mark_occurrents(&family.body, is_occurrent);
					mark_occurrents(&body.body, is_occurrent);
				}
				Obterm::Let { ty, argument, tail } => {
					mark_occurrents(ty, is_occurrent);
					mark_occurrents(argument, is_occurrent);
					mark_occurrents(&tail.body, is_occurrent);
				}
				Obterm::Pi { base, family, base_universe: _, family_universe: _ }
				| Obterm::Sigma { base, family, base_universe: _, family_universe: _ } => {
					mark_occurrents(base, is_occurrent);
					mark_occurrents(&family.body, is_occurrent);
				}
				Obterm::CaseNat { scrutinee, motive, case_nil, case_suc } => {
					mark_occurrents(scrutinee, is_occurrent);
					mark_occurrents(&motive.body, is_occurrent);
					mark_occurrents(case_nil, is_occurrent);
					mark_occurrents(&case_suc.body, is_occurrent);
				}
				Obterm::CaseBool { scrutinee, motive, case_false, case_true } => {
					mark_occurrents(scrutinee, is_occurrent);
					mark_occurrents(&motive.body, is_occurrent);
					mark_occurrents(case_false, is_occurrent);
					mark_occurrents(case_true, is_occurrent);
				}

				// 0-recursive cases.
				Obterm::Universe(_) | Obterm::Bool | Obterm::BoolValue(_) | Obterm::Nat | Obterm::Num(_) => (),

				// 1-recursive cases.
				Obterm::Project(a, _)
				| Obterm::Suc(a)
				| Obterm::WrapType(a)
				| Obterm::WrapNew(a)
				| Obterm::Unwrap(a)
				| Obterm::RcType(a)
				| Obterm::RcNew(a)
				| Obterm::UnRc(a) => mark_occurrents(a, is_occurrent),

				// 2-recursive cases.
				Obterm::Apply { scrutinee: a, argument: b } | Obterm::Pair { basepoint: a, fiberpoint: b } => {
					mark_occurrents(a, is_occurrent);
					mark_occurrents(b, is_occurrent);
				}
			}
		}

		let mut is_occurrent = vec![false; level];
		mark_occurrents(self, &mut is_occurrent);
		is_occurrent
	}
}
