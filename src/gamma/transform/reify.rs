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

pub trait Unevaluate {
	type Term;
	/// Transforms a value into a core term.
	fn unevaluate(&self) -> Self::Term {
		self.unevaluate_in(Level(0))
	}

	fn unevaluate_in(&self, level: Level) -> Self::Term;
}

impl<const N: usize> Unevaluate for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn unevaluate_in(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).unevaluate_in(level + N)))
	}
}

impl<const N: usize> Unevaluate for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn unevaluate_in(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).unevaluate_in(level + N)))
	}
}

impl Unevaluate for StaticNeutral {
	type Term = StaticTerm;
	fn unevaluate_in(&self, level @ Level(context_length): Level) -> Self::Term {
		use StaticNeutral::*;
		match self {
			Variable(name, Level(level)) => StaticTerm::Variable(*name, Index(context_length - 1 - level)),
			MaxCopyability(a, b) =>
				StaticTerm::MaxCopyability(bx!(a.unevaluate_in(level)), bx!(b.unevaluate_in(level))),
			ReprUniv(c) => StaticTerm::ReprUniv(bx!(c.unevaluate_in(level))),
			Apply(callee, argument) => StaticTerm::Apply {
				scrutinee: bx!(callee.unevaluate_in(level)),
				argument: bx!(argument.unevaluate_in(level)),
			},
			Project(scrutinee, projection) =>
				StaticTerm::Project(bx!(scrutinee.unevaluate_in(level)), *projection),
			Suc(prev) => StaticTerm::Suc(bx!(prev.unevaluate_in(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: bx!(scrutinee.unevaluate_in(level)),
				motive: motive.unevaluate_in(level),
				case_nil: bx!(case_nil.unevaluate_in(level)),
				case_suc: case_suc.unevaluate_in(level),
			},
			CaseEnum { scrutinee, motive, cases } => StaticTerm::CaseEnum {
				scrutinee: bx!(scrutinee.unevaluate_in(level)),
				motive: motive.unevaluate_in(level),
				cases: cases.into_iter().map(|case| case.unevaluate_in(level)).collect(),
			},
		}
	}
}

impl Unevaluate for StaticValue {
	type Term = StaticTerm;
	fn unevaluate_in(&self, level: Level) -> Self::Term {
		use StaticValue::*;
		match self {
			Neutral(neutral) => neutral.unevaluate_in(level),
			Universe => StaticTerm::Universe,
			IndexedProduct(base, family) =>
				StaticTerm::Pi(bx!(base.unevaluate_in(level)), family.unevaluate_in(level)),
			Function(function) => StaticTerm::Lambda(function.unevaluate_in(level)),
			IndexedSum(base, family) =>
				StaticTerm::Sigma(bx!(base.unevaluate_in(level)), family.unevaluate_in(level)),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: bx!(basepoint.unevaluate_in(level)),
				fiberpoint: bx!(fiberpoint.unevaluate_in(level)),
			},
			Lift { ty: liftee, copy, repr } => StaticTerm::Lift {
				liftee: liftee.unevaluate_in(level).into(),
				copy: copy.unevaluate_in(level).into(),
				repr: repr.unevaluate_in(level).into(),
			},
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.unevaluate_in(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Enum(k) => StaticTerm::Enum(*k),
			EnumValue(k, v) => StaticTerm::EnumValue(*k, *v),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(r0, r1) => StaticTerm::ReprPair(bx!(r0.unevaluate_in(level)), bx!(r1.unevaluate_in(level))),
			ReprMax(r0, r1) => StaticTerm::ReprMax(bx!(r0.unevaluate_in(level)), bx!(r1.unevaluate_in(level))),
		}
	}
}

impl Unevaluate for DynamicNeutral {
	type Term = DynamicTerm;
	fn unevaluate_in(&self, level @ Level(context_length): Level) -> Self::Term {
		use DynamicNeutral::*;
		match self {
			Variable(name, Level(level)) => DynamicTerm::Variable(*name, Index(context_length - 1 - level)),
			Splice(splicee) => DynamicTerm::Splice(bx!(splicee.unevaluate_in(level))),
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicTerm::Apply {
					scrutinee: bx!(scrutinee.unevaluate_in(level)),
					argument: bx!(argument.unevaluate_in(level)),
					fiber_copyability: bx!(fiber_copyability.as_ref().unwrap().unevaluate_in(level)),
					fiber_representation: bx!(fiber_representation.as_ref().unwrap().unevaluate_in(level)),
					base: base.as_ref().unwrap().unevaluate_in(level).into(),
					family: family.as_ref().unwrap().unevaluate_in(level),
				},
			Project { scrutinee, projection, copyability, representation } => DynamicTerm::Project {
				scrutinee: scrutinee.unevaluate_in(level).into(),
				projection: *projection,
				projection_copyability: copyability.as_ref().unwrap().unevaluate_in(level).into(),
				projection_representation: representation.as_ref().unwrap().unevaluate_in(level).into(),
			},
			Suc(prev) => DynamicTerm::Suc(bx!(prev.unevaluate_in(level))),
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseNat {
					scrutinee: bx!(scrutinee.unevaluate_in(level)),
					case_nil: bx!(case_nil.unevaluate_in(level)),
					case_suc: case_suc.unevaluate_in(level),
					fiber_copyability: bx!(fiber_copyability.unevaluate_in(level)),
					fiber_representation: bx!(fiber_representation.unevaluate_in(level)),
					motive: motive.unevaluate_in(level),
				},
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseEnum {
					scrutinee: bx!(scrutinee.unevaluate_in(level)),
					cases: cases.into_iter().map(|case| case.unevaluate_in(level)).collect(),
					fiber_copyability: bx!(fiber_copyability.unevaluate_in(level)),
					fiber_representation: bx!(fiber_representation.unevaluate_in(level)),
					motive: motive.unevaluate_in(level),
				},
			Unwrap { scrutinee, copyability, representation } => DynamicTerm::Unwrap {
				scrutinee: scrutinee.unevaluate_in(level).into(),
				copyability: copyability.unevaluate_in(level).into(),
				representation: representation.unevaluate_in(level).into(),
			},
			UnRc { scrutinee, copyability, representation } => DynamicTerm::UnRc {
				scrutinee: scrutinee.unevaluate_in(level).into(),
				copyability: copyability.unevaluate_in(level).into(),
				representation: representation.unevaluate_in(level).into(),
			},
		}
	}
}

impl Unevaluate for DynamicValue {
	type Term = DynamicTerm;
	fn unevaluate_in(&self, level: Level) -> Self::Term {
		use DynamicValue::*;
		match self {
			Neutral(neutral) => neutral.unevaluate_in(level),
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: bx!(copyability.unevaluate_in(level)),
				representation: bx!(representation.unevaluate_in(level)),
			},
			IndexedProduct {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				base_copyability: base_copyability.unevaluate_in(level).into(),
				base_representation: base_representation.unevaluate_in(level).into(),
				base: base.unevaluate_in(level).into(),
				family_copyability: base_copyability.unevaluate_in(level).into(),
				family_representation: base_representation.unevaluate_in(level).into(),
				family: family.unevaluate_in(level),
			},
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unevaluate_in(level).into(),
				family: family.unevaluate_in(level).into(),
				body: body.unevaluate_in(level).into(),
			},
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Sigma {
				base_copyability: base_copyability.unevaluate_in(level).into(),
				base_representation: base_representation.unevaluate_in(level).into(),
				base: base.unevaluate_in(level).into(),
				family_copyability: base_copyability.unevaluate_in(level).into(),
				family_representation: base_representation.unevaluate_in(level).into(),
				family: family.unevaluate_in(level),
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unevaluate_in(level)),
				fiberpoint: bx!(fiberpoint.unevaluate_in(level)),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),
			WrapType { inner, copyability, representation } => DynamicTerm::WrapType {
				inner: inner.unevaluate_in(level).into(),
				copyability: copyability.unevaluate_in(level).into(),
				representation: representation.unevaluate_in(level).into(),
			},
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.unevaluate_in(level))),
			RcType { inner, copyability, representation } => DynamicTerm::RcType {
				inner: inner.unevaluate_in(level).into(),
				copyability: copyability.unevaluate_in(level).into(),
				representation: representation.unevaluate_in(level).into(),
			},
			RcNew(x) => DynamicTerm::RcNew(bx!(x.unevaluate_in(level))),
		}
	}
}
