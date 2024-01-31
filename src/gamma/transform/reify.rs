use crate::{
	gamma::{
		common::{bind, Binder, Closure, Index, Level},
		ir::{
			domain::{Autolyze, DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue},
			syntax::{DynamicTerm, StaticTerm},
		},
	},
	utility::bx,
};

pub trait Reify {
	type Term;
	/// Transforms a value into a core term.
	fn reify(&self) -> Self::Term {
		self.reify_in(Level(0))
	}

	fn reify_in(&self, level: Level) -> Self::Term;
}

impl<const N: usize> Reify for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn reify_in(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify_in(level + N)))
	}
}

impl<const N: usize> Reify for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn reify_in(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify_in(level + N)))
	}
}

impl Reify for StaticNeutral {
	type Term = StaticTerm;
	fn reify_in(&self, level @ Level(context_length): Level) -> Self::Term {
		use StaticNeutral::*;
		match self {
			Variable(name, Level(level)) => StaticTerm::Variable(*name, Index(context_length - 1 - level)),
			MaxCopyability(a, b) => StaticTerm::MaxCopyability(bx!(a.reify_in(level)), bx!(b.reify_in(level))),
			ReprUniv(c) => StaticTerm::ReprUniv(bx!(c.reify_in(level))),
			Apply(callee, argument) => StaticTerm::Apply {
				scrutinee: bx!(callee.reify_in(level)),
				argument: bx!(argument.reify_in(level)),
			},
			Project(scrutinee, projection) => StaticTerm::Project(bx!(scrutinee.reify_in(level)), *projection),
			Suc(prev) => StaticTerm::Suc(bx!(prev.reify_in(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify_in(level)),
				motive: motive.reify_in(level),
				case_nil: bx!(case_nil.reify_in(level)),
				case_suc: case_suc.reify_in(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => StaticTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify_in(level)),
				motive: motive.reify_in(level),
				case_false: bx!(case_false.reify_in(level)),
				case_true: bx!(case_true.reify_in(level)),
			},
		}
	}
}

impl Reify for StaticValue {
	type Term = StaticTerm;
	fn reify_in(&self, level: Level) -> Self::Term {
		use StaticValue::*;
		match self {
			Neutral(neutral) => neutral.reify_in(level),
			Universe => StaticTerm::Universe,
			IndexedProduct(base, family) => StaticTerm::Pi(bx!(base.reify_in(level)), family.reify_in(level)),
			Function(function) => StaticTerm::Lambda(function.reify_in(level)),
			IndexedSum(base, family) => StaticTerm::Sigma(bx!(base.reify_in(level)), family.reify_in(level)),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: bx!(basepoint.reify_in(level)),
				fiberpoint: bx!(fiberpoint.reify_in(level)),
			},
			Lift(liftee) => StaticTerm::Lift(bx!(liftee.reify_in(level))),
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.reify_in(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Bool => StaticTerm::Bool,
			BoolValue(b) => StaticTerm::BoolValue(*b),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(r0, r1) => StaticTerm::ReprPair(bx!(r0.reify_in(level)), bx!(r1.reify_in(level))),
			ReprMax(r0, r1) => StaticTerm::ReprMax(bx!(r0.reify_in(level)), bx!(r1.reify_in(level))),
		}
	}
}

impl Reify for DynamicNeutral {
	type Term = DynamicTerm;
	fn reify_in(&self, level @ Level(context_length): Level) -> Self::Term {
		use DynamicNeutral::*;
		match self {
			Variable(name, Level(level)) => DynamicTerm::Variable(*name, Index(context_length - 1 - level)),
			Splice(splicee) => DynamicTerm::Splice(bx!(splicee.reify_in(level))),
			Apply(callee, argument) => DynamicTerm::Apply {
				scrutinee: bx!(callee.reify_in(level)),
				argument: bx!(argument.reify_in(level)),
			},
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.reify_in(level)), *projection),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.reify_in(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify_in(level)),
				motive: motive.reify_in(level),
				case_nil: bx!(case_nil.reify_in(level)),
				case_suc: case_suc.reify_in(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify_in(level)),
				motive: motive.reify_in(level),
				case_false: bx!(case_false.reify_in(level)),
				case_true: bx!(case_true.reify_in(level)),
			},
			Unwrap(v) => DynamicTerm::Unwrap(bx!(v.reify_in(level))),
			UnRc(v) => DynamicTerm::UnRc(bx!(v.reify_in(level))),
		}
	}
}

impl Reify for DynamicValue {
	type Term = DynamicTerm;
	fn reify_in(&self, level: Level) -> Self::Term {
		use DynamicValue::*;
		match self {
			Neutral(neutral) => neutral.reify_in(level),
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: bx!(copyability.reify_in(level)),
				representation: bx!(representation.reify_in(level)),
			},
			IndexedProduct {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				base_copyability: base_copyability.reify_in(level).into(),
				base_representation: base_representation.reify_in(level).into(),
				base: base.reify_in(level).into(),
				family_copyability: base_copyability.reify_in(level).into(),
				family_representation: base_representation.reify_in(level).into(),
				family: family.reify_in(level),
			},
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.reify_in(level).into(),
				family: family.reify_in(level).into(),
				body: body.reify_in(level).into(),
			},
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Sigma {
				base_copyability: base_copyability.reify_in(level).into(),
				base_representation: base_representation.reify_in(level).into(),
				base: base.reify_in(level).into(),
				family_copyability: base_copyability.reify_in(level).into(),
				family_representation: base_representation.reify_in(level).into(),
				family: family.reify_in(level),
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: bx!(basepoint.reify_in(level)),
				fiberpoint: bx!(fiberpoint.reify_in(level)),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			WrapType(x) => DynamicTerm::WrapType(bx!(x.reify_in(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.reify_in(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.reify_in(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.reify_in(level))),
		}
	}
}
