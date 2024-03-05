use crate::{
	gamma::{
		common::{Binder, Closure, Field, Level},
		ir::{
			domain::{DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue, Value},
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
			MaxCopyability(a, b) => {
				let a = a.evaluate_in(environment);
				let b = b.evaluate_in(environment);
				StaticValue::max_copyability(a, b)
			}
			ReprType => StaticValue::ReprType,
			ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			ReprPair(r0, r1) => {
				let r0 = r0.evaluate_in(environment);
				let r1 = r1.evaluate_in(environment);
				StaticValue::pair_representation(r0, r1)
			}
			ReprMax(r0, r1) => {
				let r0 = r0.evaluate_in(environment);
				let r1 = r1.evaluate_in(environment);
				StaticValue::max_representation(r0, r1)
			}
			ReprUniv(c) => {
				let c = c.evaluate_in(environment);
				StaticValue::univ_representation(c)
			}
			Pi(base, family) => StaticValue::IndexedProduct(
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
			Sigma(base, family) =>
				StaticValue::IndexedSum(rc!(base.evaluate_in(environment)), rc!(family.evaluate_in(environment))),
			Pair { basepoint, fiberpoint } => StaticValue::Pair(
				rc!(basepoint.evaluate_in(environment)),
				rc!(fiberpoint.evaluate_in(environment)),
			),
			Project(scrutinee, projection) => match scrutinee.evaluate_in(environment) {
				StaticValue::Pair(basepoint, fiberpoint) => match projection {
					Field::Base => basepoint.as_ref().clone(),
					Field::Fiber => fiberpoint.as_ref().clone(),
				},
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Project(rc!(neutral), projection)),
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
			Nat => StaticValue::Nat,
			Num(n) => StaticValue::Num(n),
			Suc(prev) => match prev.evaluate_in(environment) {
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Suc(rc!(neutral))),
				StaticValue::Num(n) => StaticValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate_in(environment) {
				StaticValue::Num(n) => (0..n).fold(case_nil.evaluate_in(environment), |previous, i| {
					case_suc.evaluate_at(environment, [StaticValue::Num(i), previous])
				}),
				StaticValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let StaticNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(&previous);
					}
					let result = StaticValue::Neutral(StaticNeutral::CaseNat {
						scrutinee: rc!(neutrals.pop().unwrap().clone()),
						motive: rc!(motive.evaluate_in(environment)),
						case_nil: rc!(case_nil.evaluate_in(environment)),
						case_suc: rc!(case_suc.clone().evaluate_in(environment)),
					});
					neutrals
						.into_iter()
						.rev()
						.cloned()
						.map(StaticValue::Neutral)
						.fold(result, |previous, number| case_suc.evaluate_at(environment, [number, previous]))
				}
				_ => panic!(),
			},
			Enum(card) => StaticValue::Enum(card),
			EnumValue(k, v) => StaticValue::EnumValue(k, v),
			CaseEnum { scrutinee, motive, cases } => match scrutinee.evaluate_in(environment) {
				StaticValue::EnumValue(_, v) => cases.into_iter().nth(v.into()).unwrap().evaluate_in(environment),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::CaseEnum {
					scrutinee: rc!(neutral),
					motive: rc!(motive.evaluate_in(environment)),
					cases: cases.into_iter().map(|case| case.evaluate_in(environment)).collect(),
				}),
				_ => panic!(),
			},
		}
	}
}

impl Evaluate for DynamicTerm {
	type Value = DynamicValue;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => DynamicValue::Function {
				base: base.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
				body: body.evaluate_in(environment).into(),
			},
			Pair { basepoint, fiberpoint } => DynamicValue::Pair(
				rc!(basepoint.evaluate_in(environment)),
				rc!(fiberpoint.evaluate_in(environment)),
			),
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
			Project { scrutinee, projection, projection_copyability, projection_representation } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Pair(basepoint, fiberpoint) => match projection {
						Field::Base => basepoint.as_ref().clone(),
						Field::Fiber => fiberpoint.as_ref().clone(),
					},
					DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Project {
						scrutinee: neutral.into(),
						projection,
						copyability: Some(projection_copyability.evaluate_in(environment).into()),
						representation: Some(projection_representation.evaluate_in(environment).into()),
					}),
					_ => panic!(),
				},
			Pi {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedProduct {
				base_copyability: base_copyability.evaluate_in(environment).into(),
				base_representation: base_representation.evaluate_in(environment).into(),
				base: base.evaluate_in(environment).into(),
				family_copyability: family_copyability.evaluate_in(environment).into(),
				family_representation: family_representation.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedSum {
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
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => match prev.evaluate_in(environment) {
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Suc(rc!(neutral))),
				DynamicValue::Num(n) => DynamicValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Num(n) => (0..n).fold(case_nil.evaluate_in(environment), |previous, i| {
						case_suc.evaluate_at(environment, [DynamicValue::Num(i), previous])
					}),
					DynamicValue::Neutral(neutral) => {
						let mut neutrals = vec![&neutral];
						while let DynamicNeutral::Suc(previous) = neutrals.last().unwrap() {
							neutrals.push(&previous);
						}
						let result = DynamicValue::Neutral(DynamicNeutral::CaseNat {
							scrutinee: rc!(neutrals.pop().unwrap().clone()),
							case_nil: rc!(case_nil.evaluate_in(environment)),
							case_suc: rc!(case_suc.clone().evaluate_in(environment)),
							fiber_copyability: fiber_copyability.evaluate_in(environment).into(),
							fiber_representation: fiber_representation.evaluate_in(environment).into(),
							motive: rc!(motive.evaluate_in(environment)),
						});
						neutrals
							.into_iter()
							.rev()
							.cloned()
							.map(DynamicValue::Neutral)
							.fold(result, |previous, number| case_suc.evaluate_at(environment, [number, previous]))
					}
					_ => panic!(),
				},
			Enum(k) => DynamicValue::Enum(k),
			EnumValue(k, v) => DynamicValue::EnumValue(k, v),
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::EnumValue(_, v) =>
						cases.into_iter().nth(v.into()).unwrap().evaluate_in(environment),
					DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::CaseEnum {
						scrutinee: rc!(neutral),
						cases: cases.into_iter().map(|case| case.evaluate_in(environment)).collect(),
						fiber_copyability: fiber_copyability.evaluate_in(environment).into(),
						fiber_representation: fiber_representation.evaluate_in(environment).into(),
						motive: rc!(motive.evaluate_in(environment)),
					}),
					_ => panic!(),
				},
			WrapType { inner, copyability, representation } => DynamicValue::WrapType {
				inner: inner.evaluate_in(environment).into(),
				copyability: copyability.evaluate_in(environment).into(),
				representation: representation.evaluate_in(environment).into(),
			},
			WrapNew(tm) => DynamicValue::WrapNew(rc!(tm.evaluate_in(environment))),
			Unwrap { scrutinee, copyability, representation } => match scrutinee.evaluate_in(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::Unwrap {
					scrutinee: n.into(),
					copyability: copyability.evaluate_in(environment).into(),
					representation: representation.evaluate_in(environment).into(),
				}),
				DynamicValue::WrapNew(v) => v.as_ref().clone(),
				_ => panic!(),
			},
			RcType { inner, copyability, representation } => DynamicValue::RcType {
				inner: inner.evaluate_in(environment).into(),
				copyability: copyability.evaluate_in(environment).into(),
				representation: representation.evaluate_in(environment).into(),
			},
			RcNew(tm) => DynamicValue::RcNew(rc!(tm.evaluate_in(environment))),
			UnRc { scrutinee, copyability, representation } => match scrutinee.evaluate_in(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::UnRc {
					scrutinee: n.into(),
					copyability: copyability.evaluate_in(environment).into(),
					representation: representation.evaluate_in(environment).into(),
				}),
				DynamicValue::RcNew(v) => v.as_ref().clone(),
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

pub trait Autolyze {
	type Value;
	/// Evaluates a closure on its own parameters by postulating them and passing them in.
	fn autolyze(&self, context_len: Level) -> Self::Value;
}

impl<const N: usize> Autolyze for Closure<Environment, StaticTerm, N> {
	type Value = StaticValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}

impl<const N: usize> Autolyze for Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}
