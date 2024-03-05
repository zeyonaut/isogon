use super::evaluate::Autolyze;
use crate::{
	gamma::{
		common::{bind, Binder, Closure, Index, Level},
		ir::{
			domain::{DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue},
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
			CaseEnum { scrutinee, motive, cases } => StaticTerm::CaseEnum {
				scrutinee: bx!(scrutinee.reify_in(level)),
				motive: motive.reify_in(level),
				cases: cases.into_iter().map(|case| case.reify_in(level)).collect(),
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
			Lift { ty: liftee, copy, repr } => StaticTerm::Lift {
				liftee: liftee.reify_in(level).into(),
				copy: copy.reify_in(level).into(),
				repr: repr.reify_in(level).into(),
			},
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.reify_in(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Enum(k) => StaticTerm::Enum(*k),
			EnumValue(k, v) => StaticTerm::EnumValue(*k, *v),
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
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicTerm::Apply {
					scrutinee: bx!(scrutinee.reify_in(level)),
					argument: bx!(argument.reify_in(level)),
					fiber_copyability: bx!(fiber_copyability.as_ref().unwrap().reify_in(level)),
					fiber_representation: bx!(fiber_representation.as_ref().unwrap().reify_in(level)),
					base: base.as_ref().unwrap().reify_in(level).into(),
					family: family.as_ref().unwrap().reify_in(level),
				},
			Project { scrutinee, projection, copyability, representation } => DynamicTerm::Project {
				scrutinee: scrutinee.reify_in(level).into(),
				projection: *projection,
				projection_copyability: copyability.as_ref().unwrap().reify_in(level).into(),
				projection_representation: representation.as_ref().unwrap().reify_in(level).into(),
			},
			Suc(prev) => DynamicTerm::Suc(bx!(prev.reify_in(level))),
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseNat {
					scrutinee: bx!(scrutinee.reify_in(level)),
					case_nil: bx!(case_nil.reify_in(level)),
					case_suc: case_suc.reify_in(level),
					fiber_copyability: bx!(fiber_copyability.reify_in(level)),
					fiber_representation: bx!(fiber_representation.reify_in(level)),
					motive: motive.reify_in(level),
				},
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseEnum {
					scrutinee: bx!(scrutinee.reify_in(level)),
					cases: cases.into_iter().map(|case| case.reify_in(level)).collect(),
					fiber_copyability: bx!(fiber_copyability.reify_in(level)),
					fiber_representation: bx!(fiber_representation.reify_in(level)),
					motive: motive.reify_in(level),
				},
			Unwrap { scrutinee, copyability, representation } => DynamicTerm::Unwrap {
				scrutinee: scrutinee.reify_in(level).into(),
				copyability: copyability.reify_in(level).into(),
				representation: representation.reify_in(level).into(),
			},
			UnRc { scrutinee, copyability, representation } => DynamicTerm::UnRc {
				scrutinee: scrutinee.reify_in(level).into(),
				copyability: copyability.reify_in(level).into(),
				representation: representation.reify_in(level).into(),
			},
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
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),
			WrapType { inner, copyability, representation } => DynamicTerm::WrapType {
				inner: inner.reify_in(level).into(),
				copyability: copyability.reify_in(level).into(),
				representation: representation.reify_in(level).into(),
			},
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.reify_in(level))),
			RcType { inner, copyability, representation } => DynamicTerm::RcType {
				inner: inner.reify_in(level).into(),
				copyability: copyability.reify_in(level).into(),
				representation: representation.reify_in(level).into(),
			},
			RcNew(x) => DynamicTerm::RcNew(bx!(x.reify_in(level))),
		}
	}
}
