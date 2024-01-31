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

impl DynamicValue {
	pub fn reify_closed(&self) -> DynamicTerm {
		self.reify(Level(0))
	}
}

pub trait Reify {
	type Term;
	/// Transforms a value into a core term.
	fn reify(&self, level: Level) -> Self::Term;
}

impl<const N: usize> Reify for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn reify(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify(level + N)))
	}
}

impl<const N: usize> Reify for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn reify(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify(level + N)))
	}
}

impl Reify for StaticNeutral {
	type Term = StaticTerm;
	fn reify(&self, level @ Level(context_length): Level) -> Self::Term {
		use StaticNeutral::*;
		match self {
			Variable(name, Level(level)) => StaticTerm::Variable(*name, Index(context_length - 1 - level)),
			MaxCopyability(a, b) => StaticTerm::MaxCopyability(bx!(a.reify(level)), bx!(b.reify(level))),
			ReprUniv(c) => StaticTerm::ReprUniv(bx!(c.reify(level))),
			Apply(callee, argument) =>
				StaticTerm::Apply { scrutinee: bx!(callee.reify(level)), argument: bx!(argument.reify(level)) },
			Project(scrutinee, projection) => StaticTerm::Project(bx!(scrutinee.reify(level)), *projection),
			Suc(prev) => StaticTerm::Suc(bx!(prev.reify(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_nil: bx!(case_nil.reify(level)),
				case_suc: case_suc.reify(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => StaticTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_false: bx!(case_false.reify(level)),
				case_true: bx!(case_true.reify(level)),
			},
		}
	}
}

impl Reify for StaticValue {
	type Term = StaticTerm;
	fn reify(&self, level: Level) -> Self::Term {
		use StaticValue::*;
		match self {
			Neutral(neutral) => neutral.reify(level),
			Universe => StaticTerm::Universe,
			IndexedProduct(base, family) => StaticTerm::Pi(bx!(base.reify(level)), family.reify(level)),
			Function(function) => StaticTerm::Lambda(function.reify(level)),
			IndexedSum(base, family) => StaticTerm::Sigma(bx!(base.reify(level)), family.reify(level)),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: bx!(basepoint.reify(level)),
				fiberpoint: bx!(fiberpoint.reify(level)),
			},
			Lift(liftee) => StaticTerm::Lift(bx!(liftee.reify(level))),
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.reify(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Bool => StaticTerm::Bool,
			BoolValue(b) => StaticTerm::BoolValue(*b),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(r0, r1) => StaticTerm::ReprPair(bx!(r0.reify(level)), bx!(r1.reify(level))),
			ReprMax(r0, r1) => StaticTerm::ReprMax(bx!(r0.reify(level)), bx!(r1.reify(level))),
		}
	}
}

impl Reify for DynamicNeutral {
	type Term = DynamicTerm;
	fn reify(&self, level @ Level(context_length): Level) -> Self::Term {
		use DynamicNeutral::*;
		match self {
			Variable(name, Level(level)) => DynamicTerm::Variable(*name, Index(context_length - 1 - level)),
			Splice(splicee) => DynamicTerm::Splice(bx!(splicee.reify(level))),
			Apply(callee, argument) =>
				DynamicTerm::Apply { scrutinee: bx!(callee.reify(level)), argument: bx!(argument.reify(level)) },
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.reify(level)), *projection),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.reify(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_nil: bx!(case_nil.reify(level)),
				case_suc: case_suc.reify(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_false: bx!(case_false.reify(level)),
				case_true: bx!(case_true.reify(level)),
			},
			Unwrap(v) => DynamicTerm::Unwrap(bx!(v.reify(level))),
			UnRc(v) => DynamicTerm::UnRc(bx!(v.reify(level))),
		}
	}
}

impl Reify for DynamicValue {
	type Term = DynamicTerm;
	fn reify(&self, level: Level) -> Self::Term {
		use DynamicValue::*;
		match self {
			Neutral(neutral) => neutral.reify(level),
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: bx!(copyability.reify(level)),
				representation: bx!(representation.reify(level)),
			},
			IndexedProduct {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				base_copyability: base_copyability.reify(level).into(),
				base_representation: base_representation.reify(level).into(),
				base: base.reify(level).into(),
				family_copyability: base_copyability.reify(level).into(),
				family_representation: base_representation.reify(level).into(),
				family: family.reify(level),
			},
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.reify(level).into(),
				family: family.reify(level).into(),
				body: body.reify(level).into(),
			},
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Sigma {
				base_copyability: base_copyability.reify(level).into(),
				base_representation: base_representation.reify(level).into(),
				base: base.reify(level).into(),
				family_copyability: base_copyability.reify(level).into(),
				family_representation: base_representation.reify(level).into(),
				family: family.reify(level),
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: bx!(basepoint.reify(level)),
				fiberpoint: bx!(fiberpoint.reify(level)),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			WrapType(x) => DynamicTerm::WrapType(bx!(x.reify(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.reify(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.reify(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.reify(level))),
		}
	}
}
