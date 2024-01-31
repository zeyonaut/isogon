use crate::{
	gamma::{
		common::{Binder, Closure, Projection},
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
	fn evaluate(self, environment: &Environment) -> Self::Value;
}

impl<T, const N: usize> Evaluate for Binder<Box<T>, N> {
	type Value = Closure<Environment, T, N>;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Evaluate for StaticTerm {
	type Value = StaticValue;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		use StaticTerm::*;
		match self {
			Variable(_, index) => environment.lookup_static(index),
			CopyabilityType => StaticValue::CopyabilityType,
			Copyability(c) => StaticValue::Copyability(c),
			MaxCopyability(a, b) => {
				let a = a.evaluate(environment);
				let b = b.evaluate(environment);
				StaticValue::max_copyability(a, b)
			}
			ReprType => StaticValue::ReprType,
			ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			ReprPair(r0, r1) => {
				let r0 = r0.evaluate(environment);
				let r1 = r1.evaluate(environment);
				StaticValue::pair_representation(r0, r1)
			}
			ReprMax(r0, r1) => {
				let r0 = r0.evaluate(environment);
				let r1 = r1.evaluate(environment);
				StaticValue::max_representation(r0, r1)
			}
			ReprUniv(c) => {
				let c = c.evaluate(environment);
				StaticValue::univ_representation(c)
			}
			Pi(base, family) =>
				StaticValue::IndexedProduct(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Lambda(function) => StaticValue::Function(rc!(function.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				StaticValue::Function(function) => function.evaluate_with([argument.evaluate(environment)]),
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Apply(rc!(neutral), rc!(argument.evaluate(environment)))),
				_ => panic!(),
			},
			Sigma(base, family) =>
				StaticValue::IndexedSum(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Pair { basepoint, fiberpoint } =>
				StaticValue::Pair(rc!(basepoint.evaluate(environment)), rc!(fiberpoint.evaluate(environment))),
			Project(scrutinee, projection) => match scrutinee.evaluate(environment) {
				StaticValue::Pair(basepoint, fiberpoint) => match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				},
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Project(rc!(neutral), projection)),
				_ => panic!(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate(environment)]),
			Universe => StaticValue::Universe,
			Lift(liftee) => StaticValue::Lift(liftee.evaluate(environment)),
			Quote(quotee) => StaticValue::Quote(quotee.evaluate(environment)),
			Nat => StaticValue::Nat,
			Num(n) => StaticValue::Num(n),
			Suc(prev) => match prev.evaluate(environment) {
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Suc(rc!(neutral))),
				StaticValue::Num(n) => StaticValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate(environment) {
				StaticValue::Num(n) => (0..n).fold(case_nil.evaluate(environment), |previous, i| {
					case_suc.evaluate_at(environment, [StaticValue::Num(i), previous])
				}),
				StaticValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let StaticNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(&previous);
					}
					let result = StaticValue::Neutral(StaticNeutral::CaseNat {
						scrutinee: rc!(neutrals.pop().unwrap().clone()),
						motive: rc!(motive.evaluate(environment)),
						case_nil: rc!(case_nil.evaluate(environment)),
						case_suc: rc!(case_suc.clone().evaluate(environment)),
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
			Bool => StaticValue::Bool,
			BoolValue(b) => StaticValue::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => match scrutinee.evaluate(environment) {
				StaticValue::BoolValue(b) => if b { case_true } else { case_false }.evaluate(environment),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::CaseBool {
					scrutinee: rc!(neutral),
					motive: rc!(motive.evaluate(environment)),
					case_false: rc!(case_false.evaluate(environment)),
					case_true: rc!(case_true.evaluate(environment)),
				}),
				_ => panic!(),
			},
		}
	}
}

impl Evaluate for DynamicTerm {
	type Value = DynamicValue;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => DynamicValue::Function {
				base: base.evaluate(environment).into(),
				family: family.evaluate(environment).into(),
				body: body.evaluate(environment).into(),
			},
			Pair { basepoint, fiberpoint } =>
				DynamicValue::Pair(rc!(basepoint.evaluate(environment)), rc!(fiberpoint.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				DynamicValue::Function { body, .. } => body.evaluate_with([argument.evaluate(environment)]),
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Apply(rc!(neutral), rc!(argument.evaluate(environment)))),
				_ => panic!(),
			},
			Project(scrutinee, projection) => match scrutinee.evaluate(environment) {
				DynamicValue::Pair(basepoint, fiberpoint) => match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				},
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Project(rc!(neutral), projection)),
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
				base_copyability: base_copyability.evaluate(environment).into(),
				base_representation: base_representation.evaluate(environment).into(),
				base: base.evaluate(environment).into(),
				family_copyability: family_copyability.evaluate(environment).into(),
				family_representation: family_representation.evaluate(environment).into(),
				family: family.evaluate(environment).into(),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedSum {
				base_copyability: base_copyability.evaluate(environment).into(),
				base_representation: base_representation.evaluate(environment).into(),
				base: base.evaluate(environment).into(),
				family_copyability: family_copyability.evaluate(environment).into(),
				family_representation: family_representation.evaluate(environment).into(),
				family: family.evaluate(environment).into(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate(environment)]),
			Universe { copyability, representation } => DynamicValue::Universe {
				copyability: rc!(copyability.evaluate(environment)),
				representation: rc!(representation.evaluate(environment)),
			},
			Splice(splicee) => match splicee.evaluate(environment) {
				StaticValue::Quote(quotee) => quotee,
				StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
				_ => panic!(),
			},
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => match prev.evaluate(environment) {
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Suc(rc!(neutral))),
				DynamicValue::Num(n) => DynamicValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate(environment) {
				DynamicValue::Num(n) => (0..n).fold(case_nil.evaluate(environment), |previous, i| {
					case_suc.evaluate_at(environment, [DynamicValue::Num(i), previous])
				}),
				DynamicValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let DynamicNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(&previous);
					}
					let result = DynamicValue::Neutral(DynamicNeutral::CaseNat {
						scrutinee: rc!(neutrals.pop().unwrap().clone()),
						motive: rc!(motive.evaluate(environment)),
						case_nil: rc!(case_nil.evaluate(environment)),
						case_suc: rc!(case_suc.clone().evaluate(environment)),
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
			Bool => DynamicValue::Bool,
			BoolValue(b) => DynamicValue::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => match scrutinee.evaluate(environment) {
				DynamicValue::BoolValue(b) => if b { case_true } else { case_false }.evaluate(environment),
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::CaseBool {
					scrutinee: rc!(neutral),
					motive: rc!(motive.evaluate(environment)),
					case_false: rc!(case_false.evaluate(environment)),
					case_true: rc!(case_true.evaluate(environment)),
				}),
				_ => panic!(),
			},
			WrapType(ty) => DynamicValue::WrapType(rc!(ty.evaluate(environment))),
			WrapNew(tm) => DynamicValue::WrapNew(rc!(tm.evaluate(environment))),
			Unwrap(tm) => match tm.evaluate(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::Unwrap(rc!(n))),
				DynamicValue::WrapNew(v) => v.as_ref().clone(),
				_ => panic!(),
			},
			RcType(ty) => DynamicValue::RcType(rc!(ty.evaluate(environment))),
			RcNew(tm) => DynamicValue::RcNew(rc!(tm.evaluate(environment))),
			UnRc(tm) => match tm.evaluate(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::UnRc(rc!(n))),
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
		self.body.clone().evaluate(&self.environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateWith<N> for &Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&self.environment.extend(arguments.map(Value::Dynamic)))
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
		self.body.clone().evaluate(&environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateAt<N> for &Binder<Box<DynamicTerm>, N> {
	type Value = DynamicValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&environment.extend(arguments.map(Value::Dynamic)))
	}
}
