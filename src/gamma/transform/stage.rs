use std::rc::Rc;

use crate::{
	gamma::{
		common::{Binder, Closure, Copyability, Projection, Repr, ReprAtom, UniverseKind},
		ir::{
			object::{Environment, Metavalue, Term, Value},
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
	type ObjectTerm = Metavalue;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		match self {
			StaticTerm::Variable(_, index) => environment.lookup_static(index),
			StaticTerm::CopyabilityType => Metavalue::Type,
			StaticTerm::Copyability(c) => Metavalue::Copyability(c),
			StaticTerm::MaxCopyability(a, b) => {
				let Metavalue::Copyability(a) = a.stage_in(environment) else { panic!() };
				let Metavalue::Copyability(b) = b.stage_in(environment) else { panic!() };
				Metavalue::Copyability(std::cmp::max(a, b))
			}
			StaticTerm::Lambda(function) => Metavalue::Function(function.stage_in(environment)),
			StaticTerm::Apply { scrutinee, argument } => {
				let Metavalue::Function(function) = scrutinee.stage_in(environment) else { panic!() };
				// TODO: The environment argument is useless in this position: make a separate trait for this (as in EvaluateWith/EvaluateAt).
				function.stage_with(environment, [argument.stage_in(environment)])
			}
			StaticTerm::Pi(..) => Metavalue::Type,
			StaticTerm::Sigma(..) => Metavalue::Type,
			StaticTerm::Pair { basepoint, fiberpoint } =>
				Metavalue::Pair(rc!(basepoint.stage_in(environment)), rc!(fiberpoint.stage_in(environment))),
			StaticTerm::Project(scrutinee, projection) => {
				let Metavalue::Pair(basepoint, fiberpoint) = scrutinee.stage_in(environment) else { panic!() };
				match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			StaticTerm::Let { argument, tail, .. } =>
				tail.stage_with(environment, [argument.stage_in(environment)]),
			StaticTerm::Universe => Metavalue::Type,
			StaticTerm::Lift { .. } => Metavalue::Type,
			StaticTerm::Quote(term) => Metavalue::Quote(rc!(term.stage_in(environment))),
			StaticTerm::Nat => Metavalue::Type,
			StaticTerm::Num(n) => Metavalue::Num(n),
			StaticTerm::Suc(p) => {
				let Metavalue::Num(p) = p.stage_in(environment) else { panic!() };
				Metavalue::Num(p + 1)
			}
			StaticTerm::CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let Metavalue::Num(n) = scrutinee.stage_in(environment) else { panic!() };
				(0..n).fold(case_nil.stage_in(environment), |previous, i| {
					case_suc.clone().stage_with(environment, [Metavalue::Num(i), previous])
				})
			}
			StaticTerm::Bool => Metavalue::Type,
			StaticTerm::BoolValue(b) => Metavalue::BoolValue(b),
			StaticTerm::CaseBool { scrutinee, motive: _, case_false, case_true } => {
				let Metavalue::BoolValue(b) = scrutinee.stage_in(environment) else { panic!() };
				if b { case_true } else { case_false }.stage_in(environment)
			}
			StaticTerm::ReprType => Metavalue::Type,
			StaticTerm::ReprAtom(r) => Metavalue::Repr(r.map(Repr::Atom)),
			StaticTerm::ReprPair(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage_in(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage_in(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Pair(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprMax(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage_in(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage_in(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Max(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprUniv(c) => {
				let Metavalue::Copyability(c) = c.stage_in(environment) else { panic!() };
				match c {
					Copyability::Trivial => Metavalue::Repr(None),
					Copyability::Nontrivial => Metavalue::Repr(Some(Repr::Atom(ReprAtom::Class))),
				}
			}
		}
	}
}

impl<const N: usize> Stage for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = Binder<Rc<Term>, N>;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		self.mapv(|parameters, body| body.stage_in(&environment.bind(parameters)))
	}
}

fn stage_as_dynamic_universe(
	copyability: StaticTerm,
	representation: StaticTerm,
	environment: &Environment,
) -> UniverseKind {
	let Metavalue::Repr(r) = representation.stage_in(environment) else { panic!() };
	let Metavalue::Copyability(c) = copyability.stage_in(environment) else { panic!("") };
	UniverseKind(c, r)
}

impl Stage for DynamicTerm {
	type ObjectTerm = Term;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => Term::Function {
				base: base.stage_in(environment).into(),
				body: body.stage_in(environment).into(),
				family: family.stage_in(environment).into(),
			},
			Pair { basepoint, fiberpoint } => Term::Pair {
				basepoint: rc!(basepoint.stage_in(environment)),
				fiberpoint: rc!(fiberpoint.stage_in(environment)),
			},
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				Term::Apply {
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
				Term::Project(
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
			} => Term::Pi {
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
			} => Term::Sigma {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, environment),
				base: rc!(base.stage_in(environment)),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					environment,
				),
				family: family.stage_in(environment),
			},
			Let { ty, argument, tail } => Term::Let {
				ty: rc!(ty.stage_in(environment)),
				argument: rc!(argument.stage_in(environment)),
				tail: tail.stage_in(environment),
			},
			Universe { copyability, representation } => {
				let Metavalue::Copyability(c) = copyability.stage_in(environment) else { panic!() };
				let Metavalue::Repr(r) = representation.stage_in(environment) else { panic!() };
				Term::Universe(UniverseKind(c, r))
			}
			Splice(term) => {
				let Metavalue::Quote(value) = term.stage_in(environment) else { panic!() };
				value.as_ref().clone()
			}
			Nat => Term::Nat,
			Num(n) => Term::Num(n),
			Suc(prev) => Term::Suc(rc!(prev.stage_in(environment))),
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				Term::CaseNat {
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
			Bool => Term::Bool,
			BoolValue(b) => Term::BoolValue(b),
			CaseBool { scrutinee, case_false, case_true, fiber_copyability, fiber_representation, motive } =>
				Term::CaseBool {
					scrutinee: rc!(scrutinee.stage_in(environment)),
					case_false: rc!(case_false.stage_in(environment)),
					case_true: rc!(case_true.stage_in(environment)),
					fiber_universe: stage_as_dynamic_universe(
						*fiber_copyability,
						*fiber_representation,
						environment,
					),
					motive: motive.stage_in(environment),
				},
			WrapType { inner, copyability, representation } => Term::WrapType(
				inner.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			WrapNew(x) => Term::WrapNew(rc!(x.stage_in(environment))),
			Unwrap { scrutinee, copyability, representation } => Term::Unwrap(
				scrutinee.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			RcType { inner, copyability, representation } => Term::RcType(
				inner.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
			RcNew(x) => Term::RcNew(rc!(x.stage_in(environment))),
			UnRc { scrutinee, copyability, representation } => Term::UnRc(
				scrutinee.stage_in(environment).into(),
				stage_as_dynamic_universe(*copyability, *representation, environment),
			),
		}
	}
}

pub trait StageWith<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_with(self, environment: &Environment, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageWith<N> for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Metavalue;
	fn stage_with(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&environment.extend(terms.map(Value::Static)))
	}
}

impl<const N: usize> StageWith<N> for Closure<Environment, StaticTerm, N> {
	type ObjectTerm = Metavalue;
	fn stage_with(self, _: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&self.environment.extend(terms.map(Value::Static)))
	}
}
