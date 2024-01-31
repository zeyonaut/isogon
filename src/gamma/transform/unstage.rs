use std::rc::Rc;

use crate::{
	gamma::{
		common::{Binder, Index, Level, Repr, UniverseKind},
		ir::{
			object::Term,
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

impl<const N: usize> Unstage for Binder<Rc<Term>, N> {
	type CoreTerm = Binder<Box<DynamicTerm>, N>;
	fn unstage_in(&self, context_len: Level) -> Self::CoreTerm {
		self.map_ref(|body| bx!(body.unstage_in(context_len + N)))
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

impl Unstage for Term {
	type CoreTerm = DynamicTerm;
	fn unstage_in(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use Term::*;
		match self {
			Variable(name, Level(variable)) => DynamicTerm::Variable(*name, Index(context_len - 1 - variable)),
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unstage_in(level).into(),
				family: family.unstage_in(level),
				body: body.unstage_in(level),
			},
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unstage_in(level)),
				fiberpoint: bx!(fiberpoint.unstage_in(level)),
			},
			Apply { scrutinee, argument } => DynamicTerm::Apply {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				argument: bx!(argument.unstage_in(level)),
			},
			Project(scrutinee, projection) =>
				DynamicTerm::Project(bx!(scrutinee.unstage_in(level)), *projection),
			Pi { base_universe, base, family_universe, family } => DynamicTerm::Pi {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage_in(level)),
				family: family.unstage_in(level),
				family_copyability: StaticTerm::Copyability(base_universe.0).into(),
				family_representation: StaticTerm::from(family_universe.1.as_ref()).into(),
			},
			Sigma { base_universe, base, family_universe, family } => DynamicTerm::Sigma {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage_in(level)),
				family: family.unstage_in(level),
				family_copyability: StaticTerm::Copyability(base_universe.0).into(),
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
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				motive: motive.unstage_in(level),
				case_nil: bx!(case_nil.unstage_in(level)),
				case_suc: case_suc.unstage_in(level),
			},
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.unstage_in(level)),
				motive: motive.unstage_in(level),
				case_false: bx!(case_false.unstage_in(level)),
				case_true: bx!(case_true.unstage_in(level)),
			},
			WrapType(x) => DynamicTerm::WrapType(bx!(x.unstage_in(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.unstage_in(level))),
			Unwrap(x) => DynamicTerm::Unwrap(bx!(x.unstage_in(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.unstage_in(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.unstage_in(level))),
			UnRc(x) => DynamicTerm::UnRc(bx!(x.unstage_in(level))),
		}
	}
}
