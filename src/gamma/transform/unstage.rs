use std::rc::Rc;

use crate::{
	gamma::{
		common::{Binder, Index, Level, Repr, UniverseKind},
		ir::{
			object::Obterm,
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::bx,
};

pub trait Unstage {
	type CoreTerm;
	/// Transforms an object term into a core term.
	fn unstage(&self, context_len: Level) -> Self::CoreTerm;
}

impl<const N: usize> Unstage for Binder<Rc<Obterm>, N> {
	type CoreTerm = Binder<Box<DynamicTerm>, N>;
	fn unstage(&self, context_len: Level) -> Self::CoreTerm {
		self.map_ref(|body| bx!(body.unstage(context_len + N)))
	}
}

impl Unstage for Repr {
	type CoreTerm = StaticTerm;
	fn unstage(&self, level: Level) -> Self::CoreTerm {
		match self {
			Repr::Atom(r) => StaticTerm::ReprAtom(Some(*r)),
			Repr::Pair(r0, r1) => StaticTerm::ReprPair(bx!(r0.unstage(level)), bx!(r1.unstage(level))),
			Repr::Max(r0, r1) => StaticTerm::ReprMax(bx!(r0.unstage(level)), bx!(r1.unstage(level))),
		}
	}
}

impl Unstage for Obterm {
	type CoreTerm = DynamicTerm;
	fn unstage(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use Obterm::*;
		match self {
			Variable(name, Level(variable)) => DynamicTerm::Variable(*name, Index(context_len - 1 - variable)),
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unstage(level).into(),
				family: family.unstage(level),
				body: body.unstage(level),
			},
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unstage(level)),
				fiberpoint: bx!(fiberpoint.unstage(level)),
			},
			Apply { scrutinee, argument } => DynamicTerm::Apply {
				scrutinee: bx!(scrutinee.unstage(level)),
				argument: bx!(argument.unstage(level)),
			},
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.unstage(level)), *projection),
			Pi { base_universe, base, family_universe, family } => DynamicTerm::Pi {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage(level)),
				family: family.unstage(level),
				family_copyability: StaticTerm::Copyability(base_universe.0).into(),
				family_representation: StaticTerm::from(family_universe.1.as_ref()).into(),
			},
			Sigma { base_universe, base, family_universe, family } => DynamicTerm::Sigma {
				base_copyability: StaticTerm::Copyability(base_universe.0).into(),
				base_representation: StaticTerm::from(base_universe.1.as_ref()).into(),
				base: bx!(base.unstage(level)),
				family: family.unstage(level),
				family_copyability: StaticTerm::Copyability(base_universe.0).into(),
				family_representation: StaticTerm::from(family_universe.1.as_ref()).into(),
			},
			Let { ty, argument, tail } => DynamicTerm::Let {
				ty: bx!(ty.unstage(level)),
				argument: bx!(argument.unstage(level)),
				tail: tail.unstage(level),
			},
			Universe(UniverseKind(copyability, representation)) => DynamicTerm::Universe {
				copyability: bx!(StaticTerm::Copyability(*copyability)),
				representation: bx!(representation
					.clone()
					.map(|representation| representation.unstage(level))
					.unwrap_or(StaticTerm::ReprAtom(None))),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.unstage(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_nil: bx!(case_nil.unstage(level)),
				case_suc: case_suc.unstage(level),
			},
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_false: bx!(case_false.unstage(level)),
				case_true: bx!(case_true.unstage(level)),
			},
			WrapType(x) => DynamicTerm::WrapType(bx!(x.unstage(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.unstage(level))),
			Unwrap(x) => DynamicTerm::Unwrap(bx!(x.unstage(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.unstage(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.unstage(level))),
			UnRc(x) => DynamicTerm::UnRc(bx!(x.unstage(level))),
		}
	}
}
