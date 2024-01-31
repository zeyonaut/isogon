use std::rc::Rc;

use crate::{
	gamma::{
		common::{Binder, Closure, Copyability, Projection, Repr, ReprAtom, UniverseKind},
		ir::{
			object::{Environment, Metavalue, Obterm, Value},
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::rc,
};

pub trait Stage {
	type ObjectTerm;
	/// Transforms a core term into an object term.
	fn stage(self, environment: &Environment) -> Self::ObjectTerm;
}

impl<const N: usize> Stage for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Closure<Environment, StaticTerm, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Stage for StaticTerm {
	type ObjectTerm = Metavalue;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		match self {
			StaticTerm::Variable(_, index) => environment.lookup_static(index),
			StaticTerm::CopyabilityType => Metavalue::Type,
			StaticTerm::Copyability(c) => Metavalue::Copyability(c),
			StaticTerm::MaxCopyability(a, b) => {
				let Metavalue::Copyability(a) = a.stage(environment) else { panic!() };
				let Metavalue::Copyability(b) = b.stage(environment) else { panic!() };
				Metavalue::Copyability(std::cmp::max(a, b))
			}
			StaticTerm::Lambda(function) => Metavalue::Function(function.stage(environment)),
			StaticTerm::Apply { scrutinee, argument } => {
				let Metavalue::Function(function) = scrutinee.stage(environment) else { panic!() };
				// TODO: The environment argument is useless in this position: make a separate trait for this (as in EvaluateWith/EvaluateAt).
				function.stage_with(environment, [argument.stage(environment)])
			}
			StaticTerm::Pi(..) => Metavalue::Type,
			StaticTerm::Sigma(..) => Metavalue::Type,
			StaticTerm::Pair { basepoint, fiberpoint } =>
				Metavalue::Pair(rc!(basepoint.stage(environment)), rc!(fiberpoint.stage(environment))),
			StaticTerm::Project(scrutinee, projection) => {
				let Metavalue::Pair(basepoint, fiberpoint) = scrutinee.stage(environment) else { panic!() };
				match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			StaticTerm::Let { argument, tail, .. } =>
				tail.stage_with(environment, [argument.stage(environment)]),
			StaticTerm::Universe => Metavalue::Type,
			StaticTerm::Lift(_) => Metavalue::Type,
			StaticTerm::Quote(term) => Metavalue::Quote(rc!(term.stage(environment))),
			StaticTerm::Nat => Metavalue::Type,
			StaticTerm::Num(n) => Metavalue::Num(n),
			StaticTerm::Suc(p) => {
				let Metavalue::Num(p) = p.stage(environment) else { panic!() };
				Metavalue::Num(p + 1)
			}
			StaticTerm::CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let Metavalue::Num(n) = scrutinee.stage(environment) else { panic!() };
				(0..n).fold(case_nil.stage(environment), |previous, i| {
					case_suc.clone().stage_with(environment, [Metavalue::Num(i), previous])
				})
			}
			StaticTerm::Bool => Metavalue::Type,
			StaticTerm::BoolValue(b) => Metavalue::BoolValue(b),
			StaticTerm::CaseBool { scrutinee, motive: _, case_false, case_true } => {
				let Metavalue::BoolValue(b) = scrutinee.stage(environment) else { panic!() };
				if b { case_true } else { case_false }.stage(environment)
			}
			StaticTerm::ReprType => Metavalue::Type,
			StaticTerm::ReprAtom(r) => Metavalue::Repr(r.map(Repr::Atom)),
			StaticTerm::ReprPair(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Pair(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprMax(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Max(rc!(r0), rc!(r1)))),
				}
			}
			StaticTerm::ReprUniv(c) => {
				let Metavalue::Copyability(c) = c.stage(environment) else { panic!() };
				match c {
					Copyability::Trivial => Metavalue::Repr(None),
					Copyability::Nontrivial => Metavalue::Repr(Some(Repr::Atom(ReprAtom::Class))),
				}
			}
		}
	}
}

impl<const N: usize> Stage for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = Binder<Rc<Obterm>, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		self.mapv(|parameters, body| body.stage(&environment.bind(parameters)))
	}
}

fn stage_as_dynamic_universe(
	copyability: StaticTerm,
	representation: StaticTerm,
	environment: &Environment,
) -> UniverseKind {
	let Metavalue::Repr(r) = representation.stage(environment) else { panic!() };
	let Metavalue::Copyability(c) = copyability.stage(environment) else { panic!("") };
	UniverseKind(c, r)
}

impl Stage for DynamicTerm {
	type ObjectTerm = Obterm;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => Obterm::Function {
				base: base.stage(environment).into(),
				body: body.stage(environment).into(),
				family: family.stage(environment).into(),
			},
			Pair { basepoint, fiberpoint } => Obterm::Pair {
				basepoint: rc!(basepoint.stage(environment)),
				fiberpoint: rc!(fiberpoint.stage(environment)),
			},
			Apply { scrutinee, argument } => Obterm::Apply {
				scrutinee: rc!(scrutinee.stage(environment)),
				argument: rc!(argument.stage(environment)),
			},
			Project(scrutinee, projection) => Obterm::Project(rc!(scrutinee.stage(environment)), projection),
			Pi {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => Obterm::Pi {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, environment),
				base: rc!(base.stage(environment)),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					environment,
				),
				family: family.stage(environment),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => Obterm::Sigma {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, environment),
				base: rc!(base.stage(environment)),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					environment,
				),
				family: family.stage(environment),
			},
			Let { ty, argument, tail } => Obterm::Let {
				ty: rc!(ty.stage(environment)),
				argument: rc!(argument.stage(environment)),
				tail: tail.stage(environment),
			},
			Universe { copyability, representation } => {
				let Metavalue::Copyability(c) = copyability.stage(environment) else { panic!() };
				let Metavalue::Repr(r) = representation.stage(environment) else { panic!() };
				Obterm::Universe(UniverseKind(c, r))
			}
			Splice(term) => {
				let Metavalue::Quote(value) = term.stage(environment) else { panic!() };
				value.as_ref().clone()
			}
			Nat => Obterm::Nat,
			Num(n) => Obterm::Num(n),
			Suc(prev) => Obterm::Suc(rc!(prev.stage(environment))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => Obterm::CaseNat {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_nil: rc!(case_nil.stage(environment)),
				case_suc: case_suc.stage(environment),
			},
			Bool => Obterm::Bool,
			BoolValue(b) => Obterm::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => Obterm::CaseBool {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_false: rc!(case_false.stage(environment)),
				case_true: rc!(case_true.stage(environment)),
			},
			WrapType(x) => Obterm::WrapType(rc!(x.stage(environment))),
			WrapNew(x) => Obterm::WrapNew(rc!(x.stage(environment))),
			Unwrap(x) => Obterm::Unwrap(rc!(x.stage(environment))),
			RcType(x) => Obterm::RcType(rc!(x.stage(environment))),
			RcNew(x) => Obterm::RcNew(rc!(x.stage(environment))),
			UnRc(x) => Obterm::UnRc(rc!(x.stage(environment))),
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
		self.body.stage(&environment.extend(terms.map(Value::Static)))
	}
}

impl<const N: usize> StageWith<N> for Closure<Environment, StaticTerm, N> {
	type ObjectTerm = Metavalue;
	fn stage_with(self, _: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage(&self.environment.extend(terms.map(Value::Static)))
	}
}
