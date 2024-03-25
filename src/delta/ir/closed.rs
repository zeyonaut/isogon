use std::{cmp::Ordering, collections::HashMap};

use crate::gamma::common::{Binder, Field, Level, Name, Repr, UniverseKind};

#[derive(Clone, Debug)]
pub enum Variable {
	Outer(Level),
	Parameter,
	Local(Level),
}

#[derive(Clone, Debug)]
pub struct Function {
	pub procedure_id: usize,
	pub captures: Vec<Variable>,
}

#[derive(Clone, Debug)]
pub enum Term {
	Variable(Variable),
	Let {
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Universe(UniverseKind),
	Pi {
		base: Box<Self>,
		family_universe: UniverseKind,
		family: Function,
	},
	Function(Function),
	Apply {
		callee: Box<Self>,
		argument: Box<Self>,
		fiber_representation: Option<Repr>,
		family: Option<Binder<Box<Self>>>,
	},
	Sigma {
		base_universe: UniverseKind,
		base: Box<Self>,
		family_universe: UniverseKind,
		family: Function,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Field, UniverseKind),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
		fiber_representation: Option<Repr>,
		motive: Option<Binder<Box<Self>>>,
	},
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		cases: Vec<Self>,
		fiber_representation: Option<Repr>,
		motive: Option<Binder<Box<Self>>>,
	},
	WrapType(Box<Self>),
	WrapNew(Box<Self>),
	Unwrap(Box<Self>, UniverseKind),
	RcType(Box<Self>),
	RcNew(Box<Self>),
	UnRc(Box<Self>, UniverseKind),
}

pub struct Procedure {
	pub captured_parameters: Vec<(Option<Name>, Term)>,
	pub parameter: (Option<Name>, Term),
	pub body: Term,
}

pub struct Program {
	pub entry: Term,
	pub procedures: Vec<Procedure>,
}

pub trait Substitute {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level);
}

impl Substitute for Term {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		match self {
			// Variables.
			Term::Variable(variable) => substitute_variable(variable, substitution, minimum_level),
			Term::Function(function) => function.substitute(substitution, minimum_level),

			// Binding cases.
			Term::Let { ty, argument, tail } => {
				ty.substitute(substitution, minimum_level);
				argument.substitute(substitution, minimum_level);
				tail.substitute(substitution, minimum_level);
			}
			Term::Pi { base, family, .. } | Term::Sigma { base, family, .. } => {
				base.substitute(substitution, minimum_level);
				family.substitute(substitution, minimum_level);
			}
			Term::CaseNat { scrutinee, case_nil, case_suc, fiber_representation: _, motive } => {
				scrutinee.substitute(substitution, minimum_level);
				case_nil.substitute(substitution, minimum_level);
				case_suc.substitute(substitution, minimum_level);
				motive.as_mut().map(|x| x.substitute(substitution, minimum_level));
			}
			Term::CaseEnum { scrutinee, cases, fiber_representation: _, motive } => {
				scrutinee.substitute(substitution, minimum_level);
				for case in cases {
					case.substitute(substitution, minimum_level);
				}
				motive.as_mut().map(|x| x.substitute(substitution, minimum_level));
			}

			// 0-recursive cases.
			Term::Num(_) | Term::Universe(_) | Term::Nat | Term::Enum(_) | Term::EnumValue(_, _) => (),

			// 1-recursive cases.
			Term::Project(t, _, _)
			| Term::Suc(t)
			| Term::WrapType(t)
			| Term::WrapNew(t)
			| Term::Unwrap(t, _)
			| Term::RcType(t)
			| Term::RcNew(t)
			| Term::UnRc(t, _) => {
				t.substitute(substitution, minimum_level);
			}

			// n-recursive cases.
			Term::Pair { basepoint: a, fiberpoint: b } => {
				a.substitute(substitution, minimum_level);
				b.substitute(substitution, minimum_level);
			}

			Term::Apply { callee: a, argument: b, fiber_representation: _, family: c } => {
				a.substitute(substitution, minimum_level);
				b.substitute(substitution, minimum_level);
				c.as_mut().map(|c| c.substitute(substitution, minimum_level));
			}
		}
	}
}

impl<const N: usize> Substitute for Binder<Box<Term>, N> {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		self.body.substitute(substitution, minimum_level);
	}
}

impl Substitute for Function {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		for capture in &mut self.captures {
			substitute_variable(capture, substitution, minimum_level)
		}
	}
}

fn substitute_variable(variable: &mut Variable, substitution: &HashMap<Level, Level>, minimum_level: Level) {
	match variable {
		Variable::Local(level) =>
			*variable = match level.0.cmp(&minimum_level.0) {
				Ordering::Less => Variable::Outer(substitution[level]),
				Ordering::Equal => Variable::Parameter,
				Ordering::Greater => Variable::Local(Level(level.0 - minimum_level.0 - 1)),
			},
		_ => (),
	}
}
