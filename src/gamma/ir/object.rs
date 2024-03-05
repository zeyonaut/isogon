use std::{fmt::Debug, rc::Rc};

use super::syntax::StaticTerm;
use crate::gamma::common::{Binder, Closure, Copyability, Field, Index, Level, Name, Repr, UniverseKind};

#[derive(Clone)]
pub enum Metavalue {
	Type,
	Quote(Rc<Term>),
	Function(Closure<Environment, StaticTerm>),
	Pair(Rc<Self>, Rc<Self>),
	Num(usize),
	EnumValue(u8),
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
	Dynamic(Option<Name>, Level),
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
	pub fn lookup_dynamic(&self, Index(i): Index) -> Term {
		let Some(Value::Dynamic(name, level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		Term::Variable(*name, *level)
	}

	#[must_use]
	pub fn bind<const N: usize>(&self, names: [Option<Name>; N]) -> Self {
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
pub enum Term {
	Variable(Option<Name>, Level),
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
		fiber_universe: UniverseKind,
		base: Rc<Self>,
		family: Binder<Rc<Self>>,
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
	// TODO: Is this enough information? We might want more information for fiber projections (e.g. the repr of the base.)
	Project(Rc<Self>, Field, UniverseKind),
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		case_nil: Rc<Self>,
		case_suc: Binder<Rc<Self>, 2>,
		fiber_universe: UniverseKind,
		motive: Binder<Rc<Self>>,
	},
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Rc<Self>,
		cases: Vec<Self>,
		fiber_universe: UniverseKind,
		motive: Binder<Rc<Self>>,
	},
	WrapType(Rc<Self>, UniverseKind),
	WrapNew(Rc<Self>),
	Unwrap(Rc<Self>, UniverseKind),
	RcType(Rc<Self>, UniverseKind),
	RcNew(Rc<Self>),
	UnRc(Rc<Self>, UniverseKind),
}

impl Term {
	// Yields the characteristic of the subset of all levels < level that occur as a variable in a value.
	pub fn occurences(&self, Level(level): Level) -> Vec<bool> {
		fn mark_occurrents(value: &Term, is_occurrent: &mut Vec<bool>) {
			match value {
				Term::Variable(_, Level(l)) =>
					if let Some(l_is_occurrent) = is_occurrent.get_mut(*l) {
						*l_is_occurrent = true;
					},

				// Cases with binders.
				Term::Function { base, family, body } => {
					mark_occurrents(base, is_occurrent);
					mark_occurrents(&family.body, is_occurrent);
					mark_occurrents(&body.body, is_occurrent);
				}
				Term::Let { ty, argument, tail } => {
					mark_occurrents(ty, is_occurrent);
					mark_occurrents(argument, is_occurrent);
					mark_occurrents(&tail.body, is_occurrent);
				}
				Term::Pi { base, family, base_universe: _, family_universe: _ }
				| Term::Sigma { base, family, base_universe: _, family_universe: _ } => {
					mark_occurrents(base, is_occurrent);
					mark_occurrents(&family.body, is_occurrent);
				}
				Term::CaseNat { scrutinee, case_nil, case_suc, fiber_universe: _, motive } => {
					mark_occurrents(scrutinee, is_occurrent);
					mark_occurrents(case_nil, is_occurrent);
					mark_occurrents(&case_suc.body, is_occurrent);
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents(&motive.body, is_occurrent);
				}
				Term::CaseEnum { scrutinee, cases, fiber_universe: _, motive } => {
					mark_occurrents(scrutinee, is_occurrent);
					for case in cases {
						mark_occurrents(case, is_occurrent);
					}
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents(&motive.body, is_occurrent);
				}

				// 0-recursive cases.
				Term::Universe(_) | Term::Enum(_) | Term::EnumValue(_, _) | Term::Nat | Term::Num(_) => (),

				// 1-recursive cases.
				Term::Project(a, _, _)
				| Term::Suc(a)
				| Term::WrapType(a, _)
				| Term::WrapNew(a)
				| Term::Unwrap(a, _)
				| Term::RcType(a, _)
				| Term::RcNew(a)
				| Term::UnRc(a, _) => mark_occurrents(a, is_occurrent),

				// n-recursive cases.
				Term::Pair { basepoint: a, fiberpoint: b } => {
					mark_occurrents(a, is_occurrent);
					mark_occurrents(b, is_occurrent);
				}

				Term::Apply { scrutinee: a, argument: b, fiber_universe: _, base, family } => {
					mark_occurrents(a, is_occurrent);
					mark_occurrents(b, is_occurrent);
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents(&base, is_occurrent);
					mark_occurrents(&family.body, is_occurrent);
				}
			}
		}

		let mut is_occurrent = vec![false; level];
		mark_occurrents(self, &mut is_occurrent);
		is_occurrent
	}
}
