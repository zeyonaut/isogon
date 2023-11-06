use std::rc::Rc;

use super::common::{Index, Level};
use crate::utility::rc;

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Splice(Box<StaticTerm>),
}

#[derive(Clone)]
pub enum StaticNeutral {
	Variable(Level),
	Apply { callee: Rc<Self>, argument: Rc<StaticValue> },
}

#[derive(Clone)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	Lift(DynamicValue),
	Quote(DynamicValue),
	IndexedProduct(Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

#[derive(Clone)]
pub enum DynamicNeutral {
	Variable(Level),
	Apply { callee: Rc<Self>, argument: Rc<DynamicValue> },
	Splice(StaticNeutral),
}

#[derive(Clone)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe,
	IndexedProduct(Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

#[derive(Clone)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone)]
struct Environment(Vec<Value>);

impl Environment {
	fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}
	fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}
	fn extend(&self, value: Value) -> Self {
		let mut environment = self.clone();
		environment.0.push(value);
		environment
	}
}

fn evaluate_static(environment: &Environment, term: StaticTerm) -> StaticValue {
	use StaticTerm::*;
	match term {
		Variable(index) => environment.lookup_static(index),
		Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			StaticValue::Function(rc!(move |value| {
				evaluate_static(&environment.extend(Value::Static(value)), body.clone())
			}))
		}
		Apply { scrutinee, argument } => {
			let StaticValue::Function(closure) = evaluate_static(environment, *scrutinee) else { panic!() };
			let argument = evaluate_static(environment, *argument);
			closure(argument)
		}
		Pi { base, family, .. } => StaticValue::IndexedProduct(
			rc!(evaluate_static(environment, *base)),
			rc!({
				let environment = environment.clone();
				let family = *family;
				move |value| evaluate_static(&environment.extend(Value::Static(value)), family.clone())
			}),
		),
		Let { argument, tail, .. } =>
			evaluate_static(&environment.extend(Value::Static(evaluate_static(environment, *argument))), *tail),
		Universe => StaticValue::Universe,
		Lift(liftee) => StaticValue::Lift(evaluate_dynamic(environment, *liftee)),
		Quote(quotee) => StaticValue::Quote(evaluate_dynamic(environment, *quotee)),
	}
}

fn evaluate_dynamic(environment: &Environment, term: DynamicTerm) -> DynamicValue {
	use DynamicTerm::*;
	match term {
		Variable(index) => environment.lookup_dynamic(index),
		Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			DynamicValue::Function(Rc::new(move |value| {
				evaluate_dynamic(&environment.extend(Value::Dynamic(value)), body.clone())
			}))
		}
		Apply { scrutinee, argument } => {
			let DynamicValue::Function(closure) = evaluate_dynamic(environment, *scrutinee) else { panic!() };
			let argument = evaluate_dynamic(environment, *argument);
			closure(argument)
		}
		Pi { base, family, .. } => DynamicValue::IndexedProduct(
			rc!(evaluate_dynamic(environment, *base)),
			rc!({
				let environment = environment.clone();
				let family = *family;
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), family.clone())
			}),
		),
		Let { argument, tail, .. } => evaluate_dynamic(
			&environment.extend(Value::Dynamic(evaluate_dynamic(environment, *argument))),
			*tail,
		),
		Universe => DynamicValue::Universe,
		Splice(splicee) => {
			let StaticValue::Quote(quotee) = evaluate_static(environment, *splicee) else { panic!() };
			quotee
		}
	}
}

pub fn is_convertible_static(context_length: Level, left: &StaticValue, right: &StaticValue) -> bool {
	match (left, right) {
		(StaticValue::Universe, StaticValue::Universe) => true,
		(StaticValue::Lift(left), StaticValue::Lift(right)) =>
			is_convertible_dynamic(context_length, left, right),
		(StaticValue::Quote(left), StaticValue::Quote(right)) =>
			is_convertible_dynamic(context_length, left, right),
		(StaticValue::Neutral(left), StaticValue::Neutral(right)) =>
			is_convertible_static_neutral(context_length, left, right),
		(StaticValue::Function(left), StaticValue::Function(right)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
			&right(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
		),
		(left @ StaticValue::Neutral(_), StaticValue::Function(right)) => is_convertible_static(
			context_length.suc(),
			left,
			&right(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
		),
		(StaticValue::Function(left), right @ StaticValue::Neutral(_)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
			right,
		),
		(
			StaticValue::IndexedProduct(left_base, left_family),
			StaticValue::IndexedProduct(right_base, right_family),
		) =>
			is_convertible_static(context_length, &left_base, &right_base)
				&& is_convertible_static(
					context_length.suc(),
					&left_family(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
					&right_family(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
				),
		_ => false,
	}
}

pub fn is_convertible_static_neutral(
	context_length: Level,
	left: &StaticNeutral,
	right: &StaticNeutral,
) -> bool {
	match (left, right) {
		(StaticNeutral::Variable(left), StaticNeutral::Variable(right)) => left == right,
		(
			StaticNeutral::Apply { callee: left, argument: left_argument },
			StaticNeutral::Apply { callee: right, argument: right_argument },
		) =>
			is_convertible_static_neutral(context_length, left, right)
				&& is_convertible_static(context_length, left_argument.as_ref(), right_argument.as_ref()),
		_ => false,
	}
}

pub fn is_convertible_dynamic(context_length: Level, left: &DynamicValue, right: &DynamicValue) -> bool {
	match (left, right) {
		(DynamicValue::Universe, DynamicValue::Universe) => true,
		(DynamicValue::Neutral(left), DynamicValue::Neutral(right)) =>
			is_convertible_dynamic_neutral(context_length, left, right),
		(DynamicValue::Function(left), DynamicValue::Function(right)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
		),
		(left @ DynamicValue::Neutral(_), DynamicValue::Function(right)) => is_convertible_dynamic(
			context_length.suc(),
			left,
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
		),
		(DynamicValue::Function(left), right @ DynamicValue::Neutral(_)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
			right,
		),
		(
			DynamicValue::IndexedProduct(left_base, left_family),
			DynamicValue::IndexedProduct(right_base, right_family),
		) =>
			is_convertible_dynamic(context_length, &left_base, &right_base)
				&& is_convertible_dynamic(
					context_length.suc(),
					&left_family(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
					&right_family(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
				),
		_ => false,
	}
}

pub fn is_convertible_dynamic_neutral(
	context_length: Level,
	left: &DynamicNeutral,
	right: &DynamicNeutral,
) -> bool {
	match (left, right) {
		(DynamicNeutral::Variable(left), DynamicNeutral::Variable(right)) => left == right,
		(
			DynamicNeutral::Apply { callee: left, argument: left_argument },
			DynamicNeutral::Apply { callee: right, argument: right_argument },
		) =>
			is_convertible_dynamic_neutral(context_length, left, right)
				&& is_convertible_dynamic(context_length, left_argument.as_ref(), right_argument.as_ref()),
		(DynamicNeutral::Splice(left), DynamicNeutral::Splice(right)) =>
			is_convertible_static_neutral(context_length, left, right),
		_ => false,
	}
}
