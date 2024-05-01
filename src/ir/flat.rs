use std::{cmp::Ordering, collections::HashMap};

use crate::common::{Binder, Cost, Cpy, Label, Level, Name, Repr, UniverseKind};

#[derive(Clone, Debug)]
pub enum Term {
	// Irrelevant expressions.
	Irrelevant,

	// Variables.
	Variable(Option<Name>, Variable),

	// Let-expressions.
	Let {
		grade: u64,
		argument_kind: UniverseKind,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>>,
	},

	// Repeated programs.
	Repeat {
		grade: u64,
		copy: Cpy,
		term: Box<Self>,
	},
	ExpLet {
		grade: u64,
		grade_argument: u64,
		copy: Cpy,
		repr: Option<Repr>,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>>,
	},

	// Dependent functions.
	Function {
		procedure_id: usize,
		captures: Vec<Capture>,
	},
	Apply {
		callee: Box<Self>,
		argument: Box<Self>,
		result_repr: Option<Repr>,
	},

	// Dependent pairs.
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	SgLet {
		grade: u64,
		argument: Box<Self>,
		kinds: [UniverseKind; 2],
		tail: Binder<Label, Box<Self>, 2>,
	},

	// Enumerated numbers.
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		cases: Vec<Self>,
		motive_repr: Option<Repr>,
	},

	// Natural numbers.
	Num(u64),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		case_nil: Box<Self>,
		case_suc: Binder<Label, Box<Self>, 2>,
		motive_repr: Option<Repr>,
	},

	// Wrappers.
	BxValue(Box<Self>),
	BxProject(Box<Self>, Option<Repr>),

	WrapValue(Box<Self>),
	WrapProject(Box<Self>, Option<Repr>),
}

#[derive(Clone, Copy, Debug)]
pub enum Variable {
	Outer(Level),
	Parameter,
	Local(Level),
}

#[derive(Clone, Debug)]
pub struct Capture {
	pub name: Option<Name>,
	pub variable: Variable,
	pub cost: Cost,
}

#[derive(Clone, Debug)]
pub struct Parameter {
	pub name: Option<Name>,
	pub grade: Cost,
	pub repr: Option<Repr>,
}

#[derive(Debug)]
pub struct Procedure {
	pub captured_parameters: Vec<Parameter>,
	pub parameter: Option<Parameter>,
	pub body: Term,
	pub result_repr: Option<Repr>,
}

#[derive(Debug)]
pub struct Program {
	pub input: Option<(Label, UniverseKind)>,
	pub entry: Term,
	pub repr: Option<Repr>,
	pub procedures: Vec<Procedure>,
}

pub trait Substitute {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level);
}

impl Substitute for Term {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		match self {
			// Irrelevant expressions.
			Term::Irrelevant => (),

			// Variables.
			Term::Variable(_, variable) => variable.substitute(substitution, minimum_level),

			// Let-expressions.
			Term::Let { grade: _, argument_kind: _, argument, tail } => {
				argument.substitute(substitution, minimum_level);
				tail.substitute(substitution, minimum_level);
			}

			// Repeated programs.
			Term::Repeat { grade: _, copy: _, term } => term.substitute(substitution, minimum_level),
			Term::ExpLet { grade: _, grade_argument: _, copy: _, repr: _, argument, tail } => {
				argument.substitute(substitution, minimum_level);
				tail.substitute(substitution, minimum_level);
			}

			// Dependent functions.
			Term::Function { procedure_id: _, captures } =>
				for capture in captures {
					capture.variable.substitute(substitution, minimum_level)
				},
			Term::Apply { callee, argument, result_repr: _ } => {
				callee.substitute(substitution, minimum_level);
				argument.substitute(substitution, minimum_level);
			}

			// Dependent pairs.
			Term::Pair { basepoint, fiberpoint } => {
				basepoint.substitute(substitution, minimum_level);
				fiberpoint.substitute(substitution, minimum_level);
			}
			Term::SgLet { grade: _, argument, kinds: _, tail } => {
				argument.substitute(substitution, minimum_level);
				tail.substitute(substitution, minimum_level);
			}

			// Enumerated numbers.
			Term::EnumValue(_, _) => (),
			Term::CaseEnum { scrutinee, cases, motive_repr: _ } => {
				scrutinee.substitute(substitution, minimum_level);
				for case in cases {
					case.substitute(substitution, minimum_level);
				}
			}

			// Natural numbers.
			Term::Num(_) => (),
			Term::Suc(tm) => tm.substitute(substitution, minimum_level),
			Term::CaseNat { scrutinee, case_nil, case_suc, motive_repr: _ } => {
				scrutinee.substitute(substitution, minimum_level);
				case_nil.substitute(substitution, minimum_level);
				case_suc.substitute(substitution, minimum_level);
			}

			// Wrappars.
			Term::BxValue(tm) => tm.substitute(substitution, minimum_level),
			Term::BxProject(tm, _) => tm.substitute(substitution, minimum_level),

			Term::WrapValue(tm) => tm.substitute(substitution, minimum_level),
			Term::WrapProject(tm, _) => tm.substitute(substitution, minimum_level),
		}
	}
}

impl<const N: usize> Substitute for Binder<Label, Box<Term>, N> {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		self.body.substitute(substitution, minimum_level);
	}
}

impl Substitute for Variable {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		if let Variable::Local(level) = self {
			*self = match level.0.cmp(&minimum_level.0) {
				Ordering::Less => Variable::Outer(substitution[level]),
				Ordering::Equal => Variable::Parameter,
				Ordering::Greater => Variable::Local(Level(level.0 - minimum_level.0 - 1)),
			}
		}
	}
}
