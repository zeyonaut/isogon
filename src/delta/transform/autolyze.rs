use super::evaluate::EvaluateWith;
use crate::delta::{
	common::{Closure, Level},
	ir::{semantics, syntax},
};

pub trait Autolyze {
	type Value;
	/// Evaluates a closure on its own parameters by postulating them and passing them in.
	fn autolyze(&self, context_len: Level) -> Self::Value;
}

impl<const N: usize> Autolyze for Closure<semantics::Environment, syntax::StaticTerm, N> {
	type Value = semantics::StaticValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}

impl<const N: usize> Autolyze for Closure<semantics::Environment, syntax::DynamicTerm, N> {
	type Value = semantics::DynamicValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}
/*
impl<const N: usize> Autolyze for Closure<object::Environment, syntax::DynamicTerm, N> {
	type Value = object::DynamicValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.stage_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			object::DynamicValue::Variable(parameter, y)
		}))
	}
}
*/
