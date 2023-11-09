use std::{fmt::Debug, rc::Rc};

use super::{
	common::{Index, Level},
	elaborator::{DynamicTerm, StaticTerm},
};
use crate::utility::{bx, rc};

#[derive(Clone)]
pub enum StaticValue {
	Type,
	Quote(Rc<DynamicValue>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

impl Debug for StaticValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Type => write!(f, "Type"),
			Self::Quote(quotee) => f.debug_tuple("Quote").field(quotee).finish(),
			Self::Function(_) => f.debug_tuple("Function").field(&format_args!("_")).finish(),
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Variable(Level),
	Function { parameter: Rc<str>, closure: Rc<Self> },
	Apply { scrutinee: Rc<Self>, argument: Rc<Self> },
	Pi { parameter: Rc<str>, base: Rc<Self>, family: Rc<Self> },
	Let { assignee: Rc<str>, ty: Rc<Self>, argument: Rc<Self>, tail: Rc<Self> },
	Universe,
}

impl DynamicValue {
	pub fn unstage(&self) -> super::elaborator::DynamicTerm {
		fn unstage_open(
			value: &DynamicValue,
			level @ Level(context_length): Level,
		) -> super::elaborator::DynamicTerm {
			use DynamicValue::*;
			match value {
				Variable(Level(variable)) => DynamicTerm::Variable(Index(context_length - 1 - variable)),
				Function { parameter, closure } => DynamicTerm::Lambda {
					parameter: parameter.to_string(),
					body: bx!(unstage_open(&closure, level.suc())),
				},
				Apply { scrutinee, argument } => DynamicTerm::Apply {
					scrutinee: bx!(unstage_open(scrutinee, level)),
					argument: bx!(unstage_open(argument, level)),
				},
				Pi { parameter, base, family } => DynamicTerm::Pi {
					parameter: parameter.to_string(),
					base: bx!(unstage_open(base, level)),
					family: bx!(unstage_open(family, level.suc())),
				},
				Let { assignee, ty, argument, tail } => DynamicTerm::Let {
					assignee: assignee.to_string(),
					ty: bx!(unstage_open(ty, level)),
					argument: bx!(unstage_open(argument, level)),
					tail: bx!(unstage_open(tail, level.suc())),
				},
				Universe => DynamicTerm::Universe,
			}
		}

		unstage_open(self, Level(0))
	}
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(Level),
}

#[derive(Clone)]
pub struct Environment {
	values: Vec<Value>,
	dynamic_context_length: Level,
}

impl Environment {
	pub fn new() -> Self {
		Self { values: Vec::new(), dynamic_context_length: Level(0) }
	}

	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		DynamicValue::Variable(*level)
	}

	#[must_use]
	pub fn extend_static(&self, value: StaticValue) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Static(value));
		environment
	}

	#[must_use]
	pub fn extend_dynamic(&self) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Dynamic(self.dynamic_context_length));
		environment.dynamic_context_length = environment.dynamic_context_length.suc();
		environment
	}
}

pub fn evaluate_static(environment: &Environment, term: StaticTerm) -> StaticValue {
	match term {
		StaticTerm::Variable(index) => environment.lookup_static(index),
		StaticTerm::Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			StaticValue::Function(Rc::new(move |value| {
				evaluate_static(&environment.extend_static(value), body.clone())
			}))
		}
		StaticTerm::Apply { scrutinee, argument } => {
			let StaticValue::Function(closure) = evaluate_static(environment, *scrutinee) else { panic!() };
			let argument = evaluate_static(environment, *argument);
			closure(argument)
		}
		StaticTerm::Pi { .. } => StaticValue::Type,
		StaticTerm::Let { argument, tail, .. } =>
			evaluate_static(&environment.extend_static(evaluate_static(environment, *argument)), *tail),
		StaticTerm::Universe => StaticValue::Type,
		StaticTerm::Lift(_) => StaticValue::Type,
		StaticTerm::Quote(term) => StaticValue::Quote(rc!(evaluate_dynamic(environment, *term))),
	}
}

pub fn stage(term: DynamicTerm) -> DynamicValue {
	evaluate_dynamic(&Environment::new(), term)
}

pub fn evaluate_dynamic(environment: &Environment, term: DynamicTerm) -> DynamicValue {
	match term {
		DynamicTerm::Variable(index) => environment.lookup_dynamic(index),
		DynamicTerm::Lambda { parameter, body } => DynamicValue::Function {
			parameter: parameter.into(),
			closure: rc!(evaluate_dynamic(&environment.extend_dynamic(), *body)),
		},
		DynamicTerm::Apply { scrutinee, argument } => DynamicValue::Apply {
			scrutinee: rc!(evaluate_dynamic(environment, *scrutinee)),
			argument: rc!(evaluate_dynamic(environment, *argument)),
		},
		DynamicTerm::Pi { parameter, base, family } => DynamicValue::Pi {
			parameter: parameter.into(),
			base: rc!(evaluate_dynamic(environment, *base)),
			family: rc!(evaluate_dynamic(&environment.extend_dynamic(), *family)),
		},
		DynamicTerm::Let { assignee, ty, argument, tail } => {
			let ty = evaluate_dynamic(environment, *ty);
			let argument = evaluate_dynamic(environment, *argument);
			DynamicValue::Let {
				assignee: assignee.into(),
				ty: rc!(ty),
				argument: rc!(argument.clone()),
				tail: rc!(evaluate_dynamic(&environment.extend_dynamic(), *tail)),
			}
		}
		DynamicTerm::Universe => DynamicValue::Universe,
		DynamicTerm::Splice(term) => {
			let StaticValue::Quote(value) = evaluate_static(environment, *term) else { panic!() };
			value.as_ref().clone()
		}
	}
}
