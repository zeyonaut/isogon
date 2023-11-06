use std::rc::Rc;

use super::{
	common::{Index, Level},
	elaborator::{DynamicTerm, StaticTerm},
};
use crate::utility::rc;

#[derive(Clone)]
pub enum StaticValue {
	Type,
	Quote(Rc<DynamicValue>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

#[derive(Clone)]
pub enum DynamicValue {
	Variable(Level),
	Function { parameter: Rc<str>, closure: Rc<Self> },
	Apply { scrutinee: Rc<Self>, argument: Rc<Self> },
	Pi { parameter: Rc<str>, base: Rc<Self>, family: Rc<Self> },
	Let { assignee: Rc<str>, ty: Rc<Self>, argument: Rc<Self>, tail: Rc<Self> },
	Universe,
}

#[derive(Clone)]
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
	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		DynamicValue::Variable(*level)
	}
	pub fn extend_static(&self, value: StaticValue) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Static(value));
		environment
	}
	pub fn extend_dynamic(&self) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Dynamic(self.dynamic_context_length));
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
