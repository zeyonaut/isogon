use core::panic;

use crate::{
	common::{Binder, Closure, Field, Label, Level},
	ir::{
		semantics::{
			CpyValue, DynamicNeutral, DynamicValue, Environment, KindValue, StaticNeutral, StaticValue, Value,
		},
		syntax::{DynamicTerm, KindTerm, StaticTerm},
	},
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

impl<T, const N: usize> Evaluate for Binder<Label, Box<T>, N> {
	type Value = Closure<Environment, T, N>;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Evaluate for KindTerm {
	type Value = KindValue;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		KindValue { copy: self.copy.evaluate_in(environment), repr: self.repr.evaluate_in(environment) }
	}
}
impl Evaluate for StaticTerm {
	type Value = StaticValue;
	fn evaluate_in(self, environment: &Environment) -> Self::Value {
		use StaticTerm as S;
		match self {
			// Variables.
			S::Variable(_, index) => environment.lookup_static(index),

			// Let-expressions.
			S::Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),

			// Types and universe indices.
			S::Universe(c) => StaticValue::Universe(c),
			S::Cpy => StaticValue::Cpy,
			S::CpyNt => StaticValue::CpyValue(CpyValue::Nt),
			S::CpyMax(set) => set.into_iter().fold(StaticValue::CpyValue(CpyValue::Max(vec![])), |a, b| {
				StaticValue::max_copyability(environment.level(), a, b.evaluate_in(environment))
			}),
			S::Repr => StaticValue::ReprType,
			S::ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			S::ReprPair(l, r) =>
				StaticValue::pair_representation(l.evaluate_in(environment), r.evaluate_in(environment)),
			// TODO: Absorb rnone.
			S::ReprExp { len, kind } => StaticValue::exp_representation(len, kind.evaluate_in(environment)),

			// Quoted programs.
			S::Lift { liftee, kind } => StaticValue::Lift {
				ty: liftee.evaluate_in(environment),
				kind: kind.evaluate_in(environment).into(),
			},
			S::Quote(quotee) => StaticValue::Quote(quotee.evaluate_in(environment)),

			// Repeated programs.
			S::Exp(grade, c, ty) => StaticValue::Exp(grade, c, ty.evaluate_in(environment).into()),
			S::Repeat(grade, argument) => StaticValue::Repeat(grade, argument.evaluate_in(environment).into()),
			S::ExpLet { grade: _, grade_argument: _, argument, tail } =>
				tail.evaluate_at(environment, [argument.evaluate_in(environment).exp_project()]),
			S::ExpProject(t) => t.evaluate_in(environment).exp_project(),

			// Dependent functions.
			S::Pi { fragment, base_copy, base, family_copy, family } => StaticValue::IndexedProduct {
				fragment,
				base_copy,
				base: base.evaluate_in(environment).into(),
				family_copy,
				family: family.evaluate_in(environment).into(),
			},
			S::Function(grade, function) =>
				StaticValue::Function(grade, function.evaluate_in(environment).into()),
			S::Apply { scrutinee, argument } => match scrutinee.evaluate_in(environment) {
				StaticValue::Function(_, function) => function.evaluate_with([argument.evaluate_in(environment)]),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Apply(
					neutral.into(),
					argument.evaluate_in(environment).into(),
				)),
				_ => panic!(),
			},

			// Dependent pairs.
			S::Sg { base_copy, base, family_copy, family } => StaticValue::IndexedSum {
				base_copy,
				base: base.evaluate_in(environment).into(),
				family_copy,
				family: family.evaluate_in(environment).into(),
			},
			S::Pair { basepoint, fiberpoint } => StaticValue::Pair(
				basepoint.evaluate_in(environment).into(),
				fiberpoint.evaluate_in(environment).into(),
			),
			S::SgLet { grade: _, argument, tail } => {
				let argument = argument.evaluate_in(environment);
				tail.evaluate_at(
					environment,
					[argument.clone().field(Field::Base), argument.clone().field(Field::Fiber)],
				)
			}
			S::SgField(scrutinee, field) => scrutinee.evaluate_in(environment).field(field),

			// Enumerated numbers.
			S::Enum(card) => StaticValue::Enum(card),
			S::EnumValue(k, v) => StaticValue::EnumValue(k, v),
			S::CaseEnum { scrutinee, motive, cases } => match scrutinee.evaluate_in(environment) {
				StaticValue::EnumValue(_, v) => cases.into_iter().nth(v.into()).unwrap().evaluate_in(environment),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::CaseEnum {
					scrutinee: neutral.into(),
					motive: motive.evaluate_in(environment).into(),
					cases: cases.into_iter().map(|case| case.evaluate_in(environment)).collect(),
				}),
				_ => panic!(),
			},

			// Natural numbers.
			S::Nat => StaticValue::Nat,
			S::Num(n) => StaticValue::Num(n),
			S::Suc(prev) => prev.evaluate_in(environment).suc(),
			S::CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate_in(environment) {
				StaticValue::Num(n) => (0..n).fold(case_nil.evaluate_in(environment), |previous, i| {
					case_suc.evaluate_at(environment, [StaticValue::Num(i), previous])
				}),
				StaticValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let StaticNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(previous);
					}
					let result = StaticValue::Neutral(StaticNeutral::CaseNat {
						scrutinee: neutrals.pop().unwrap().clone().into(),
						motive: motive.evaluate_in(environment).into(),
						case_nil: case_nil.evaluate_in(environment).into(),
						case_suc: case_suc.clone().evaluate_in(environment).into(),
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
			Def { argument, tail, .. } =>
				tail.body.evaluate_in(&environment.extend([Value::Static(argument.evaluate_in(environment))])),
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate_in(environment)]),

			// Types.
			Universe { kind } => DynamicValue::Universe { kind: kind.evaluate_in(environment).into() },

			// Quoted programs.
			Splice(splicee) => match splicee.evaluate_in(environment) {
				StaticValue::Quote(quotee) => quotee,
				StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
				_ => panic!(),
			},

			// Repeated programs.
			Exp(grade, kind, ty) =>
				DynamicValue::Exp(grade, kind.evaluate_in(environment).into(), ty.evaluate_in(environment).into()),
			Repeat { grade, kind: _, term } => DynamicValue::Repeat(grade, term.evaluate_in(environment).into()),
			ExpLet { grade: _, grade_argument: _, argument, kind: _, tail } =>
				tail.evaluate_at(environment, [argument.evaluate_in(environment).exp_project()]),
			ExpProject(t) => t.evaluate_in(environment).exp_project(),

			// Dependent functions.
			Function { fragment, body, domain_kind: _, codomain_kind: _ } =>
				DynamicValue::Function { fragment, body: body.evaluate_in(environment).into() },
			Apply { scrutinee, fragment: _, argument, family_kind: _ } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Function { body, .. } => body.evaluate_with([argument.evaluate_in(environment)]),
					DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Apply {
						scrutinee: neutral.into(),
						argument: argument.evaluate_in(environment).into(),
					}),
					_ => panic!(),
				},
			Pi { fragment, base_kind, base, family_kind, family } => DynamicValue::IndexedProduct {
				fragment,
				base_kind: base_kind.evaluate_in(environment).into(),
				base: base.evaluate_in(environment).into(),
				family_kind: family_kind.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
			},

			// Dependent pairs.
			Sg { base_kind, base, family_kind, family } => DynamicValue::IndexedSum {
				base_kind: base_kind.evaluate_in(environment).into(),
				base: base.evaluate_in(environment).into(),
				family_kind: family_kind.evaluate_in(environment).into(),
				family: family.evaluate_in(environment).into(),
			},
			Pair { basepoint, fiberpoint } => DynamicValue::Pair(
				basepoint.evaluate_in(environment).into(),
				fiberpoint.evaluate_in(environment).into(),
			),
			SgLet { grade: _, argument, kinds: _, tail } => {
				let argument = argument.evaluate_in(environment);
				tail.evaluate_at(environment, [argument.clone().field(Field::Base), argument.field(Field::Fiber)])
			}
			SgField { scrutinee, field } => scrutinee.evaluate_in(environment).field(field),

			// Enumerated numbers.
			Enum(k) => DynamicValue::Enum(k),
			EnumValue(k, v) => DynamicValue::EnumValue(k, v),
			CaseEnum { scrutinee, cases, motive, motive_kind: _ } => match scrutinee.evaluate_in(environment) {
				DynamicValue::EnumValue(_, v) =>
					cases.into_iter().nth(v.into()).unwrap().evaluate_in(environment),
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::CaseEnum {
					scrutinee: neutral.into(),
					motive: motive.evaluate_in(environment).into(),
					cases: cases.into_iter().map(|case| case.evaluate_in(environment)).collect(),
				}),
				_ => panic!(),
			},

			// Paths.
			Id { kind, space, left, right } => DynamicValue::Id {
				kind: kind.evaluate_in(environment).into(),
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

			// Natural numbers.
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => prev.evaluate_in(environment).suc(),
			CaseNat { scrutinee, motive_kind: _, motive, case_nil, case_suc } =>
				match scrutinee.evaluate_in(environment) {
					DynamicValue::Num(n) => (0..n).fold(case_nil.evaluate_in(environment), |previous, i| {
						case_suc.evaluate_at(environment, [DynamicValue::Num(i), previous])
					}),
					DynamicValue::Neutral(neutral) => {
						let mut neutrals = vec![&neutral];
						while let DynamicNeutral::Suc(previous) = neutrals.last().unwrap() {
							neutrals.push(previous);
						}
						let result = DynamicValue::Neutral(DynamicNeutral::CaseNat {
							scrutinee: neutrals.pop().unwrap().clone().into(),
							motive: motive.evaluate_in(environment).into(),
							case_nil: case_nil.evaluate_in(environment).into(),
							case_suc: case_suc.clone().evaluate_in(environment).into(),
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

			// Wrappers.
			Bx { kind, inner } => DynamicValue::Bx {
				kind: kind.evaluate_in(environment).into(),
				inner: inner.evaluate_in(environment).into(),
			},
			BxValue(tm) => DynamicValue::BxValue(tm.evaluate_in(environment).into()),
			BxProject { scrutinee, kind: _ } => match scrutinee.evaluate_in(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::BxProject(n.into())),
				DynamicValue::BxValue(v) => v.as_ref().clone(),
				_ => panic!(),
			},
			Wrap { inner, kind } => DynamicValue::Wrap {
				inner: inner.evaluate_in(environment).into(),
				kind: kind.evaluate_in(environment).into(),
			},
			WrapValue(tm) => DynamicValue::WrapValue(tm.evaluate_in(environment).into()),
			WrapProject { scrutinee, kind: _ } => match scrutinee.evaluate_in(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::WrapProject(n.into())),
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

impl<const N: usize> EvaluateAt<N> for &Binder<Label, Box<StaticTerm>, N> {
	type Value = StaticValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateAt<N> for &Binder<Label, Box<DynamicTerm>, N> {
	type Value = DynamicValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate_in(&environment.extend(arguments.map(Value::Dynamic)))
	}
}

pub trait EvaluateAuto {
	type Value;
	/// Evaluates a closure on its own parameters by postulating them and passing them in.
	fn evaluate_auto(&self, context_len: Level) -> Self::Value;
}

impl<const N: usize> EvaluateAuto for Closure<Environment, StaticTerm, N> {
	type Value = StaticValue;
	fn evaluate_auto(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}

impl<const N: usize> EvaluateAuto for Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn evaluate_auto(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}
