use std::rc::Rc;

use crate::{
	gamma::{
		common::{Binder, Closure, Copyability, Field, Index, Repr, ReprAtom, UniverseKind},
		ir::{
			object::{DynamicValue, Environment, StaticValue, Value},
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::rc,
};

pub trait Stage {
	type ObjectTerm;
	/// Transforms a core term into an object term.
	fn stage(self) -> Self::ObjectTerm
	where
		Self: Sized,
	{
		self.stage_in(&Environment::new())
	}

	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm;
}

impl<const N: usize> Stage for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Closure<Environment, StaticTerm, N>;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Stage for StaticTerm {
	type ObjectTerm = StaticValue;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		match self {
			StaticTerm::Variable(_, index) => environment.lookup_static(index),
			StaticTerm::CopyabilityType => StaticValue::Type,
			StaticTerm::Copyability(c) => StaticValue::Copyability(c),
			StaticTerm::MaxCopyability(a, b) => {
				let StaticValue::Copyability(a) = a.stage_in(environment) else { panic!() };
				let StaticValue::Copyability(b) = b.stage_in(environment) else { panic!() };
				StaticValue::Copyability(std::cmp::max(a, b))
			}
			StaticTerm::Lambda(function) => StaticValue::Function(function.stage_in(environment)),
			StaticTerm::Apply { scrutinee, argument } => {
				let StaticValue::Function(function) = scrutinee.stage_in(environment) else { panic!() };
				// TODO: The environment argument is useless in this position: make a separate trait for this (as in EvaluateWith/EvaluateAt).
				function.stage_with([argument.stage_in(environment)])
			}
			StaticTerm::Pi(..) => StaticValue::Type,
			StaticTerm::Sigma(..) => StaticValue::Type,
			StaticTerm::Pair { basepoint, fiberpoint } =>
				StaticValue::Pair(rc!(basepoint.stage_in(environment)), rc!(fiberpoint.stage_in(environment))),
			StaticTerm::Project(scrutinee, projection) => {
				let StaticValue::Pair(basepoint, fiberpoint) = scrutinee.stage_in(environment) else { panic!() };
				match projection {
					Field::Base => basepoint.as_ref().clone(),
					Field::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			StaticTerm::Let { argument, tail, .. } =>
				tail.stage_at(environment, [argument.stage_in(environment)]),
			StaticTerm::Universe => StaticValue::Type,
			StaticTerm::Lift { .. } => StaticValue::Type,
			StaticTerm::Quote(term) => StaticValue::Quote(rc!(term.stage_in(environment))),
			StaticTerm::Nat => StaticValue::Type,
			StaticTerm::Num(n) => StaticValue::Num(n),
			StaticTerm::Suc(p) => {
				let StaticValue::Num(p) = p.stage_in(environment) else { panic!() };
				StaticValue::Num(p + 1)
			}
			StaticTerm::CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let StaticValue::Num(n) = scrutinee.stage_in(environment) else { panic!() };
				(0..n).fold(case_nil.stage_in(environment), |previous, i| {
					case_suc.clone().stage_at(environment, [StaticValue::Num(i), previous])
				})
			}
			StaticTerm::Enum(_) => StaticValue::Type,
			StaticTerm::EnumValue(_, v) => StaticValue::EnumValue(v),
			StaticTerm::CaseEnum { scrutinee, motive: _, cases } => {
				let StaticValue::EnumValue(v) = scrutinee.stage_in(environment) else { panic!() };
				cases.into_iter().nth(v as _).unwrap().stage_in(environment)
			}
			StaticTerm::ReprType => StaticValue::Type,
			StaticTerm::ReprAtom(r) => StaticValue::Repr(r.map(Repr::Atom)),
			StaticTerm::ReprPair(r0, r1) => {
				let StaticValue::Repr(r0) = r0.stage_in(environment) else { panic!() };
				let StaticValue::Repr(r1) = r1.stage_in(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => StaticValue::Repr(r1),
					(r0, None) => StaticValue::Repr(r0),
					(Some(r0), Some(r1)) => StaticValue::Repr(Some(Repr::Pair(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprMax(r0, r1) => {
				let StaticValue::Repr(r0) = r0.stage_in(environment) else { panic!() };
				let StaticValue::Repr(r1) = r1.stage_in(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => StaticValue::Repr(r1),
					(r0, None) => StaticValue::Repr(r0),
					(Some(r0), Some(r1)) => StaticValue::Repr(Some(Repr::Max(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprUniv(c) => {
				let StaticValue::Copyability(c) = c.stage_in(environment) else { panic!() };
				match c {
					Copyability::Trivial => StaticValue::Repr(None),
					Copyability::Nontrivial => StaticValue::Repr(Some(Repr::Atom(ReprAtom::Class))),
				}
			}
		}
	}
}

impl<const N: usize> Stage for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = Closure<Environment, DynamicTerm, N>;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

fn stage_as_dynamic_universe(
	copyability: StaticTerm,
	representation: StaticTerm,
	environment: &Environment,
) -> UniverseKind {
	let StaticValue::Repr(r) = representation.stage_in(environment) else { panic!() };
	let StaticValue::Copyability(c) = copyability.stage_in(environment) else { panic!("") };
	UniverseKind(c, r)
}

impl Stage for DynamicTerm {
	type ObjectTerm = DynamicValue;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => DynamicValue::Function {
				base: base.stage_in(environment).into(),
				body: body.stage_in(environment).into(),
				family: family.stage_in(environment).into(),
			},
			Pair { basepoint, fiberpoint } => DynamicValue::Pair {
				basepoint: rc!(basepoint.stage_in(environment)),
				fiberpoint: rc!(fiberpoint.stage_in(environment)),
			},
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicValue::Apply {
					scrutinee: rc!(scrutinee.stage_in(environment)),
					argument: rc!(argument.stage_in(environment)),
					fiber_universe: stage_as_dynamic_universe(
						*fiber_copyability,
						*fiber_representation,
						environment,
					),
					base: base.stage_in(environment).into(),
					family: family.stage_in(environment),
				},
			Project { scrutinee, projection, projection_copyability, projection_representation } =>
				DynamicValue::Project(
					scrutinee.stage_in(environment).into(),
					projection,
					stage_as_dynamic_universe(*projection_copyability, *projection_representation, environment),
				),
			Pi {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::Pi {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, environment),
				base: rc!(base.stage_in(environment)),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					environment,
				),
				family: family.stage_in(environment),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::Sigma {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, environment),
				base: rc!(base.stage_in(environment)),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					environment,
				),
				family: family.stage_in(environment),
			},
			Let { ty, argument, tail } => DynamicValue::Let {
				ty: rc!(ty.stage_in(environment)),
				argument: rc!(argument.stage_in(environment)),
				tail: tail.stage_in(environment),
			},
			Universe { copyability, representation } => {
				let StaticValue::Copyability(c) = copyability.stage_in(environment) else { panic!() };
				let StaticValue::Repr(r) = representation.stage_in(environment) else { panic!() };
				DynamicValue::Universe(UniverseKind(c, r))
			}
			Splice(term) => {
				let StaticValue::Quote(value) = term.stage_in(environment) else { panic!() };
				value.as_ref().clone()
			}
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => DynamicValue::Suc(rc!(prev.stage_in(environment))),
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				DynamicValue::CaseNat {
					scrutinee: rc!(scrutinee.stage_in(environment)),
					case_nil: rc!(case_nil.stage_in(environment)),
					case_suc: case_suc.stage_in(environment),
					fiber_universe: stage_as_dynamic_universe(
						*fiber_copyability,
						*fiber_representation,
						environment,
					),
					motive: motive.stage_in(environment),
				},
			Enum(k) => DynamicValue::Enum(k),
			EnumValue(k, v) => DynamicValue::EnumValue(k, v),
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				DynamicValue::CaseEnum {
					scrutinee: rc!(scrutinee.stage_in(environment)),
					cases: cases.into_iter().map(|case| case.stage_in(environment)).collect(),
					fiber_universe: stage_as_dynamic_universe(
						*fiber_copyability,
						*fiber_representation,
						environment,
					),
					motive: motive.stage_in(environment),
				},
			Id { copy, repr, space, left, right } => DynamicValue::Id {
				kind: stage_as_dynamic_universe(*copy, *repr, environment),
				space: space.stage_in(environment).into(),
				left: left.stage_in(environment).into(),
				right: right.stage_in(environment).into(),
			},
			Refl => DynamicValue::Refl,
			CasePath { scrutinee, motive, case_refl } => DynamicValue::CasePath {
				scrutinee: scrutinee.stage_in(environment).into(),
				motive: motive.stage_in(environment),
				case_refl: case_refl.stage_in(environment).into(),
			},
			WrapType { inner, copyability, representation } => DynamicValue::WrapType(
				inner.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			WrapNew(x) => DynamicValue::WrapNew(rc!(x.stage_in(environment))),
			Unwrap { scrutinee, copyability, representation } => DynamicValue::Unwrap(
				scrutinee.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			RcType { inner, copyability, representation } => DynamicValue::RcType(
				inner.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			RcNew(x) => DynamicValue::RcNew(rc!(x.stage_in(environment))),
			UnRc { scrutinee, copyability, representation } => DynamicValue::UnRc(
				scrutinee.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
		}
	}
}

pub trait StageWith<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_with(self, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageWith<N> for &Closure<Environment, DynamicTerm, N> {
	type ObjectTerm = DynamicValue;
	fn stage_with(self, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.clone().stage_in(&self.environment.extend(terms.map(Value::Dynamic)))
	}
}

impl<const N: usize> StageWith<N> for &Closure<Environment, StaticTerm, N> {
	type ObjectTerm = StaticValue;
	fn stage_with(self, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.clone().stage_in(&self.environment.extend(terms.map(Value::Static)))
	}
}

pub trait StageAt<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_at(self, environment: &Environment, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageAt<N> for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = DynamicValue;
	fn stage_at(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&environment.extend(terms.map(Value::Dynamic)))
	}
}

impl<const N: usize> StageAt<N> for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = StaticValue;
	fn stage_at(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&environment.extend(terms.map(Value::Static)))
	}
}
