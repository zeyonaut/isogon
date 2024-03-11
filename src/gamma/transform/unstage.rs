use std::rc::Rc;

use super::autolyze::Autolyze;
use crate::{
	gamma::{
		common::{bind, Binder, Closure, Index, Level, Repr, UniverseKind},
		ir::{
			object::{DynamicValue, Environment},
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::bx,
};

pub trait Unstage {
	type CoreTerm;
	/// Transforms an object term into a core term.
	fn unstage(self) -> Self::CoreTerm
	where
		Self: Sized,
	{
		self.unstage_in(Level(0))
	}

	fn unstage_in(&self, context_len: Level) -> Self::CoreTerm;
}

impl<const N: usize> Unstage for Closure<Environment, DynamicTerm, N> {
	type CoreTerm = Binder<Box<DynamicTerm>, N>;
	fn unstage_in(&self, level: Level) -> Self::CoreTerm {
		bind(self.parameters, self.autolyze(level).unstage_in(level + N))
	}
}

impl Unstage for Repr {
	type CoreTerm = StaticTerm;
	fn unstage_in(&self, level: Level) -> Self::CoreTerm {
		match self {
			Repr::Atom(r) => StaticTerm::ReprAtom(Some(*r)),
			Repr::Pair(r0, r1) => StaticTerm::ReprPair(bx!(r0.unstage_in(level)), bx!(r1.unstage_in(level))),
			Repr::Max(r0, r1) => StaticTerm::ReprMax(bx!(r0.unstage_in(level)), bx!(r1.unstage_in(level))),
		}
	}
}

impl Unstage for DynamicValue {
	type CoreTerm = DynamicTerm;
	fn unstage_in(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use DynamicValue::*;
		match self {
			Variable(name, v) => DynamicTerm::Variable(*name, Index(context_len - (v.0 + 1))),
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unstage_in(level).into(),
				family: family.unstage_in(level),
				body: body.unstage_in(level),
			},
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unstage_in(level)),
				fiberpoint: bx!(fiberpoint.unstage_in(level)),
			},
			Apply { scrutinee, argument, fiber_universe, base, family } => DynamicTerm::Apply {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				argument: bx!(argument.unstage_in(level)),
				fiber_copyability: StaticTerm::Copyability(fiber_universe.0).into(),
				fiber_representation: StaticTerm::from(fiber_universe.1.as_ref()).into(),
				base: base.unstage_in(level).into(),
				family: family.unstage_in(level),
			},
			Project(scrutinee, projection, universe) => DynamicTerm::Project {
				scrutinee: scrutinee.unstage_in(level).into(),
				projection: *projection,
				projection_copyability: StaticTerm::Copyability(universe.0).into(),
				projection_representation: StaticTerm::from(universe.1.as_ref()).into(),
			},
			Pi { base_universe, base, family_universe, family } => DynamicTerm::Pi {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage_in(level)),
				family: family.unstage_in(level),
				family_copyability: StaticTerm::Copyability(family_universe.0).into(),
				family_representation: StaticTerm::from(family_universe.1.as_ref()).into(),
			},
			Sigma { base_universe, base, family_universe, family } => DynamicTerm::Sigma {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage_in(level)),
				family: family.unstage_in(level),
				family_copyability: StaticTerm::Copyability(family_universe.0).into(),
				family_representation: StaticTerm::from(family_universe.1.as_ref()).into(),
			},
			Let { ty, argument, tail } => DynamicTerm::Let {
				ty: bx!(ty.unstage_in(level)),
				argument: bx!(argument.unstage_in(level)),
				tail: tail.unstage_in(level),
			},
			Universe(UniverseKind(copyability, representation)) => DynamicTerm::Universe {
				copyability: bx!(StaticTerm::Copyability(*copyability)),
				representation: bx!(representation
					.clone()
					.map(|representation| representation.unstage_in(level))
					.unwrap_or(StaticTerm::ReprAtom(None))),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.unstage_in(level))),
			CaseNat { scrutinee, case_nil, case_suc, fiber_universe, motive } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				case_nil: bx!(case_nil.unstage_in(level)),
				case_suc: case_suc.unstage_in(level),
				fiber_copyability: StaticTerm::Copyability(fiber_universe.0).into(),
				fiber_representation: StaticTerm::from(fiber_universe.1.as_ref()).into(),
				motive: motive.unstage_in(level),
			},
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),
			CaseEnum { scrutinee, cases, fiber_universe, motive } => DynamicTerm::CaseEnum {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				cases: cases.into_iter().map(|case| case.unstage_in(level)).collect(),
				fiber_copyability: StaticTerm::Copyability(fiber_universe.0).into(),
				fiber_representation: StaticTerm::from(fiber_universe.1.as_ref()).into(),
				motive: motive.unstage_in(level),
			},
			Id { kind, space, left, right } => DynamicTerm::Id {
				copy: StaticTerm::Copyability(kind.0).into(),
				repr: StaticTerm::from(kind.1.as_ref()).into(),
				space: space.unstage_in(level).into(),
				left: left.unstage_in(level).into(),
				right: right.unstage_in(level).into(),
			},
			Refl => DynamicTerm::Refl,
			CasePath { scrutinee, motive, case_refl } => DynamicTerm::CasePath {
				scrutinee: scrutinee.unstage_in(level).into(),
				motive: motive.unstage_in(level),
				case_refl: case_refl.unstage_in(level).into(),
			},
			WrapType(inner, universe) => DynamicTerm::WrapType {
				inner: inner.unstage_in(level).into(),
				copyability: StaticTerm::Copyability(universe.0).into(),
				representation: StaticTerm::from(universe.1.as_ref()).into(),
			},
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.unstage_in(level))),
			Unwrap(scrutinee, universe) => DynamicTerm::Unwrap {
				scrutinee: scrutinee.unstage_in(level).into(),
				copyability: StaticTerm::Copyability(universe.0).into(),
				representation: StaticTerm::from(universe.1.as_ref()).into(),
			},
			RcType(inner, universe) => DynamicTerm::RcType {
				inner: inner.unstage_in(level).into(),
				copyability: StaticTerm::Copyability(universe.0).into(),
				representation: StaticTerm::from(universe.1.as_ref()).into(),
			},
			RcNew(x) => DynamicTerm::RcNew(bx!(x.unstage_in(level))),
			UnRc(scrutinee, universe) => DynamicTerm::UnRc {
				scrutinee: scrutinee.unstage_in(level).into(),
				copyability: StaticTerm::Copyability(universe.0).into(),
				representation: StaticTerm::from(universe.1.as_ref()).into(),
			},
		}
	}
}
