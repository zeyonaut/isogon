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
			// Variables.
			Variable(_, index) => environment.lookup_static(index),

			// Let-expressions.
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),

			// Types and universe indices.
			Universe => StaticValue::Universe,
			Cpy => StaticValue::Cpy,
			CpyValue(c) => StaticValue::CpyValue(c),
			CpyMax(a, b) => StaticValue::max_copyability(a.evaluate_in(environment), b.evaluate_in(environment)),
			Repr => StaticValue::ReprType,
			ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			ReprPair(l, r) =>
				StaticValue::pair_representation(l.evaluate_in(environment), r.evaluate_in(environment)),
			// TODO: Absorb rnone.
			ReprExp(grade, repr) => StaticValue::ReprExp(grade, repr.evaluate_in(environment).into()),

			// Quoted programs.
			Lift { liftee, copy, repr } => StaticValue::Lift {
				ty: liftee.evaluate_in(environment),
				copy: copy.evaluate_in(environment).into(),
				repr: repr.evaluate_in(environment).into(),
			},
			Quote(quotee) => StaticValue::Quote(quotee.evaluate_in(environment)),

			// Repeated programs.
			Exp(grade, ty) => StaticValue::Exp(grade, ty.evaluate_in(environment).into()),
			Repeat(grade, argument) => StaticValue::Repeat(grade, argument.evaluate_in(environment).into()),
			LetExp { grade, grade_argument: _, argument, tail } => match argument.evaluate_in(environment) {
				StaticValue::Repeat(_, argument) => tail.evaluate_at(environment, [(*argument).clone()]),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::LetExp {
					scrutinee: neutral.into(),
					grade,
					tail: tail.clone().evaluate_in(environment).into(),
				}),
				_ => panic!(),
			},

			// Dependent functions.
			Pi(grade, base, family) => StaticValue::IndexedProduct(
				grade,
				base.evaluate_in(environment).into(),
				family.evaluate_in(environment).into(),
			),
			Function(grade, function) => StaticValue::Function(grade, rc!(function.evaluate_in(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate_in(environment) {
				StaticValue::Function(_, function) => function.evaluate_with([argument.evaluate_in(environment)]),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Apply(
					rc!(neutral),
					rc!(argument.evaluate_in(environment)),
				)),
				_ => panic!(),
			},

			// Dependent pairs.
			Sg(base, family) => StaticValue::IndexedSum(
				base.evaluate_in(environment).into(),
				family.evaluate_in(environment).into(),
			),
			Pair { basepoint, fiberpoint } => StaticValue::Pair(
				basepoint.evaluate_in(environment).into(),
				fiberpoint.evaluate_in(environment).into(),
			),
			SgField(scrutinee, projection) => match scrutinee.evaluate_in(environment) {
				StaticValue::Pair(basepoint, fiberpoint) => match projection {
					Field::Base => basepoint.as_ref().clone(),
					Field::Fiber => fiberpoint.as_ref().clone(),
				},
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Project(neutral.into(), projection)),
				_ => panic!(),
			},
			SgLet { grade: _, argument, tail } => tail.evaluate_at(
				environment,
				[
					SgField(argument.clone(), Field::Base).evaluate_in(environment),
					SgField(argument.clone(), Field::Fiber).evaluate_in(environment),
				],
			),

			// Enumerated numbers.
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
			// Variables.
			Variable(_, index) => environment.lookup_dynamic(index),

			// Let-expressions.
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),

			// Types.
			Universe { copyability, representation } => DynamicValue::Universe {
				copy: rc!(copyability.evaluate_in(environment)),
				repr: rc!(representation.evaluate_in(environment)),
			},

			// Quoted programs.
			Splice(splicee) => match splicee.evaluate_in(environment) {
				StaticValue::Quote(quotee) => quotee,
				StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
				_ => panic!(),
			},

			// Repeated programs.
			Exp(grade, ty) => DynamicValue::Exp(grade, ty.evaluate_in(environment).into()),
			Repeat(grade, argument) => DynamicValue::Repeat(grade, argument.evaluate_in(environment).into()),
			LetExp { grade, grade_argument: _, argument, tail } => match argument.evaluate_in(environment) {
				DynamicValue::Repeat(_, argument) => tail.evaluate_at(environment, [(*argument).clone()]),
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::LetExp {
					scrutinee: neutral.into(),
					grade,
					tail: tail.clone().evaluate_in(environment).into(),
				}),
				_ => panic!(),
			},

			// Dependent functions.
			Function { grade, base, family, body } => DynamicValue::Function {
				grade,
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

			// Dependent pairs.
			Sg { base_copy, base_repr, base, family_copy, family_repr, family } => DynamicValue::IndexedSum {
				base_copyability: base_copy.evaluate_in(environment).into(),
				base_representation: base_repr.evaluate_in(environment).into(),
				base: base.evaluate_in(environment).into(),
				family_copyability: family_copy.evaluate_in(environment).into(),
				family_representation: family_repr.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
			},
			Pair { basepoint, fiberpoint } => DynamicValue::Pair(
				basepoint.evaluate_in(environment).into(),
				fiberpoint.evaluate_in(environment).into(),
			),
			SgField { scrutinee, field } => match scrutinee.evaluate_in(environment) {
				DynamicValue::Pair(basepoint, fiberpoint) => match field {
					Field::Base => basepoint.as_ref().clone(),
					Field::Fiber => fiberpoint.as_ref().clone(),
				},
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Project { scrutinee: neutral.into(), projection: field }),
				_ => panic!(),
			},
			SgLet { grade: _, argument, tail } => tail.evaluate_at(
				environment,
				[
					SgField { scrutinee: argument.clone(), field: Field::Base }.evaluate_in(environment),
					SgField { scrutinee: argument.clone(), field: Field::Fiber }.evaluate_in(environment),
				],
			),

			// Enumerated numbers.
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

			// Paths.
			Id { copy, repr, space, left, right } => DynamicValue::Id {
				copy: copy.evaluate_in(environment).into(),
				repr: repr.evaluate_in(environment).into(),
				space: space.evaluate_in(environment).into(),
				left: left.evaluate_in(environment).into(),
				right: right.evaluate_in(environment).into(),
			},
			Refl => DynamicValue::Refl,
			CasePath { scrutinee, motive, case_refl } => match scrutinee.clone().evaluate_in(environment) {
				DynamicValue::Refl => case_refl.evaluate_in(environment),
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::CasePath {
					scrutinee: neutral.into(),
					motive: motive.evaluate_in(environment).into(),
					case_refl: case_refl.evaluate_in(environment).into(),
				}),
				_ => panic!(),
			},

			// Wrappers.
			Bx { inner, copy: copyability, repr: representation } => DynamicValue::Bx {
				inner: inner.evaluate_in(environment).into(),
				copy: copyability.evaluate_in(environment).into(),
				repr: representation.evaluate_in(environment).into(),
			},
			BxValue(tm) => DynamicValue::BxValue(rc!(tm.evaluate_in(environment))),
			BxProject { scrutinee, copy: copyability, repr: representation } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::BxProject {
						scrutinee: n.into(),
						copyability: copyability.evaluate_in(environment).into(),
						representation: representation.evaluate_in(environment).into(),
					}),
					DynamicValue::BxValue(v) => v.as_ref().clone(),
					_ => panic!(),
				},
			Wrap { inner, copy: copyability, repr: representation } => DynamicValue::Wrap {
				inner: inner.evaluate_in(environment).into(),
				copy: copyability.evaluate_in(environment).into(),
				repr: representation.evaluate_in(environment).into(),
			},
			WrapValue(tm) => DynamicValue::WrapValue(rc!(tm.evaluate_in(environment))),
			WrapProject { scrutinee, copy: copyability, repr: representation } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::WrapProject {
						scrutinee: n.into(),
						copyability: copyability.evaluate_in(environment).into(),
						representation: representation.evaluate_in(environment).into(),
					}),
					DynamicValue::WrapValue(v) => v.as_ref().clone(),
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
