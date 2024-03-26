use crate::{
	delta::{
		common::{Binder, Closure, Field},
		ir::{
			semantics::{DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue, Value},
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::rc,
};

pub trait Evaluate {
	type Value;
	/// Transforms a core term into a value.
	fn evaluate(self) -> Self::Value
	where
		Self: Sized,
	{
		self.evaluate_in(&Environment(Vec::new()))
	}

	fn evaluate_in(self, environment: &Environment) -> Self::Value;
}

impl<T, const N: usize> Evaluate for Binder<Box<T>, N> {
	type Value = Closure<Environment, T, N>;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Evaluate for StaticTerm {
	type Value = StaticValue;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		use StaticTerm::*;
		match self {
			Variable(_, index) => environment.lookup_static(index),
			CopyabilityType => StaticValue::CopyabilityType,
			Copyability(c) => StaticValue::Copyability(c),
			MaxCopyability(a, b) =>
				StaticValue::max_copyability(a.evaluate_in(environment), b.evaluate_in(environment)),
			ReprType => StaticValue::ReprType,
			ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			ReprUniv(c) => StaticValue::univ_representation(c.evaluate_in(environment)),
			Pi(grade, base, family) => StaticValue::IndexedProduct(
				grade,
				rc!(base.evaluate_in(environment)),
				rc!(family.evaluate_in(environment)),
			),
			Lambda(function) => StaticValue::Function(rc!(function.evaluate_in(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate_in(environment) {
				StaticValue::Function(function) => function.evaluate_with([argument.evaluate_in(environment)]),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Apply(
					rc!(neutral),
					rc!(argument.evaluate_in(environment)),
				)),
				_ => panic!(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),
			Universe => StaticValue::Universe,
			Lift { liftee, copy, repr } => StaticValue::Lift {
				ty: liftee.evaluate_in(environment),
				copy: copy.evaluate_in(environment).into(),
				repr: repr.evaluate_in(environment).into(),
			},
			Quote(quotee) => StaticValue::Quote(quotee.evaluate_in(environment)),
		}
	}
}

impl Evaluate for DynamicTerm {
	type Value = DynamicValue;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Function { base, family, body } => DynamicValue::Function {
				base: base.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
				body: body.evaluate_in(environment).into(),
			},
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Function { body, .. } => body.evaluate_with([argument.evaluate_in(environment)]),
					DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Apply {
						scrutinee: rc!(neutral),
						argument: rc!(argument.evaluate_in(environment)),
						fiber_copyability: Some(fiber_copyability.evaluate_in(environment).into()),
						fiber_representation: Some(fiber_representation.evaluate_in(environment).into()),
						base: Some(base.evaluate_in(environment).into()),
						family: Some(rc!(family.evaluate_in(environment))),
					}),
					_ => panic!(),
				},
			Pi {
				grade,
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedProduct {
				grade,
				base_copyability: base_copyability.evaluate_in(environment).into(),
				base_representation: base_representation.evaluate_in(environment).into(),
				base: base.evaluate_in(environment).into(),
				family_copyability: family_copyability.evaluate_in(environment).into(),
				family_representation: family_representation.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),
			Universe { copyability, representation } => DynamicValue::Universe {
				copyability: rc!(copyability.evaluate_in(environment)),
				representation: rc!(representation.evaluate_in(environment)),
			},
			Splice(splicee) => match splicee.evaluate_in(environment) {
				StaticValue::Quote(quotee) => quotee,
				StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
				_ => panic!(),
			},
		}
	}
}

pub trait EvaluateWith<const N: usize> {
	type Value;
	/// Transforms a core closure under a binder into a value, taking arguments.
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value;
}

impl<const N: usize> EvaluateWith<N> for &Closure<Environment, StaticTerm, N> {
	type Value = StaticValue;
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&self.environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateWith<N> for &Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&self.environment.extend(arguments.map(Value::Dynamic)))
	}
}

pub trait EvaluateAt<const N: usize> {
	type Value;
	/// Transforms a core term under a binder into a value, taking arguments.
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value;
}

impl<const N: usize> EvaluateAt<N> for &Binder<Box<StaticTerm>, N> {
	type Value = StaticValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateAt<N> for &Binder<Box<DynamicTerm>, N> {
	type Value = DynamicValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&environment.extend(arguments.map(Value::Dynamic)))
	}
}
