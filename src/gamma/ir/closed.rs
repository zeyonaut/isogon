use std::{cmp::Ordering, collections::HashMap};

use crate::gamma::common::{Binder, Level, Name, Projection, UniverseKind};

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
pub enum ClosedValue {
	Variable(Variable),
	Let {
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Universe(UniverseKind),
	Pi(Box<Self>, Function),
	Function(Function),
	Apply {
		callee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma(Box<Self>, Function),
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
	WrapType(Box<Self>),
	WrapNew(Box<Self>),
	Unwrap(Box<Self>),
	RcType(Box<Self>),
	RcNew(Box<Self>),
	UnRc(Box<Self>),
}

pub struct Procedure {
	pub captured_parameters: Vec<(Name, ClosedValue)>,
	pub parameter: (Name, ClosedValue),
	pub body: ClosedValue,
}

pub struct Program {
	pub entry: ClosedValue,
	pub procedures: Vec<Procedure>,
}

pub trait Substitute {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level);
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

impl Substitute for Function {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		for capture in &mut self.captures {
			substitute_variable(capture, substitution, minimum_level)
		}
	}
}

impl Substitute for ClosedValue {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		match self {
			// Variables.
			ClosedValue::Variable(variable) => substitute_variable(variable, substitution, minimum_level),
			ClosedValue::Function(function) => function.substitute(substitution, minimum_level),

			// Binding cases.
			ClosedValue::Let { ty, argument, tail } => {
				ty.substitute(substitution, minimum_level);
				argument.substitute(substitution, minimum_level);
				tail.substitute(substitution, minimum_level);
			}
			ClosedValue::Pi(base, family) | ClosedValue::Sigma(base, family) => {
				base.substitute(substitution, minimum_level);
				family.substitute(substitution, minimum_level);
			}
			ClosedValue::CaseNat { scrutinee, motive, case_nil, case_suc } => {
				scrutinee.substitute(substitution, minimum_level);
				motive.substitute(substitution, minimum_level);
				case_nil.substitute(substitution, minimum_level);
				case_suc.substitute(substitution, minimum_level);
			}
			ClosedValue::CaseBool { scrutinee, motive, case_false, case_true } => {
				scrutinee.substitute(substitution, minimum_level);
				motive.substitute(substitution, minimum_level);
				case_false.substitute(substitution, minimum_level);
				case_true.substitute(substitution, minimum_level);
			}

			// 0-recursive cases.
			ClosedValue::Num(_)
			| ClosedValue::Universe(_)
			| ClosedValue::Nat
			| ClosedValue::Bool
			| ClosedValue::BoolValue(_) => (),

			// 1-recursive cases.
			ClosedValue::Project(t, _)
			| ClosedValue::Suc(t)
			| ClosedValue::WrapType(t)
			| ClosedValue::WrapNew(t)
			| ClosedValue::Unwrap(t)
			| ClosedValue::RcType(t)
			| ClosedValue::RcNew(t)
			| ClosedValue::UnRc(t) => {
				t.substitute(substitution, minimum_level);
			}

			// 2-recursive cases.
			ClosedValue::Apply { callee: a, argument: b }
			| ClosedValue::Pair { basepoint: a, fiberpoint: b } => {
				a.substitute(substitution, minimum_level);
				b.substitute(substitution, minimum_level);
			}
		}
	}
}

impl<const N: usize> Substitute for Binder<Box<ClosedValue>, N> {
	fn substitute(&mut self, substitution: &HashMap<Level, Level>, minimum_level: Level) {
		self.body.substitute(substitution, minimum_level);
	}
}
