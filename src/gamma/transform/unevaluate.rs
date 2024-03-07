use super::evaluate::Autolyze;
use crate::gamma::{
	common::{bind, Binder, Closure, Index, Level},
	ir::{
		semantics::{DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue},
		syntax::{DynamicTerm, StaticTerm},
	},
};

pub trait Unevaluate {
	type Term;
	/// Transforms a value into a core term.
	fn unevaluate(&self) -> Self::Term {
		self.unevaluate_in(Level(0)).unwrap()
	}

	#[must_use]
	fn unevaluate_in(&self, level: Level) -> Result<Self::Term, ()>;
}

impl<const N: usize> Unevaluate for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(bind(self.parameters, self.autolyze(level).unevaluate_in(level + N)?.into()))
	}
}

impl<const N: usize> Unevaluate for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(bind(self.parameters, self.autolyze(level).unevaluate_in(level + N)?.into()))
	}
}

impl Unevaluate for StaticNeutral {
	type Term = StaticTerm;
	fn unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use StaticNeutral::*;
		Ok(match self {
			Variable(name, Level(level)) =>
				StaticTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),
			MaxCopyability(a, b) =>
				StaticTerm::MaxCopyability(a.unevaluate_in(level)?.into(), b.unevaluate_in(level)?.into()),
			ReprUniv(c) => StaticTerm::ReprUniv(c.unevaluate_in(level)?.into()),
			Apply(callee, argument) => StaticTerm::Apply {
				scrutinee: callee.unevaluate_in(level)?.into(),
				argument: argument.unevaluate_in(level)?.into(),
			},
			Project(scrutinee, projection) =>
				StaticTerm::Project(scrutinee.unevaluate_in(level)?.into(), *projection),
			Suc(prev) => StaticTerm::Suc(prev.unevaluate_in(level)?.into()),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: scrutinee.unevaluate_in(level)?.into(),
				motive: motive.unevaluate_in(level)?,
				case_nil: case_nil.unevaluate_in(level)?.into(),
				case_suc: case_suc.unevaluate_in(level)?,
			},
			CaseEnum { scrutinee, motive, cases } => StaticTerm::CaseEnum {
				scrutinee: scrutinee.unevaluate_in(level)?.into(),
				motive: motive.unevaluate_in(level)?,
				cases: cases.into_iter().map(|case| case.unevaluate_in(level)).collect::<Result<_, _>>()?,
			},
		})
	}
}

impl Unevaluate for StaticValue {
	type Term = StaticTerm;
	fn unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use StaticValue::*;
		Ok(match self {
			Neutral(neutral) => neutral.unevaluate_in(level)?,
			Universe => StaticTerm::Universe,
			IndexedProduct(base, family) =>
				StaticTerm::Pi(base.unevaluate_in(level)?.into(), family.unevaluate_in(level)?),
			Function(function) => StaticTerm::Lambda(function.unevaluate_in(level)?),
			IndexedSum(base, family) =>
				StaticTerm::Sigma(base.unevaluate_in(level)?.into(), family.unevaluate_in(level)?),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: basepoint.unevaluate_in(level)?.into(),
				fiberpoint: fiberpoint.unevaluate_in(level)?.into(),
			},
			Lift { ty: liftee, copy, repr } => StaticTerm::Lift {
				liftee: liftee.unevaluate_in(level)?.into(),
				copy: copy.unevaluate_in(level)?.into(),
				repr: repr.unevaluate_in(level)?.into(),
			},
			Quote(quotee) => StaticTerm::Quote(quotee.unevaluate_in(level)?.into()),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Enum(k) => StaticTerm::Enum(*k),
			EnumValue(k, v) => StaticTerm::EnumValue(*k, *v),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(r0, r1) =>
				StaticTerm::ReprPair(r0.unevaluate_in(level)?.into(), r1.unevaluate_in(level)?.into()),
			ReprMax(r0, r1) =>
				StaticTerm::ReprMax(r0.unevaluate_in(level)?.into(), r1.unevaluate_in(level)?.into()),
		})
	}
}

impl Unevaluate for DynamicNeutral {
	type Term = DynamicTerm;
	fn unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use DynamicNeutral::*;
		Ok(match self {
			Variable(name, Level(level)) =>
				DynamicTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),
			Splice(splicee) => DynamicTerm::Splice(splicee.unevaluate_in(level)?.into()),
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicTerm::Apply {
					scrutinee: scrutinee.unevaluate_in(level)?.into(),
					argument: argument.unevaluate_in(level)?.into(),
					fiber_copyability: fiber_copyability.as_ref().unwrap().unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.as_ref().unwrap().unevaluate_in(level)?.into(),
					base: base.as_ref().unwrap().unevaluate_in(level)?.into(),
					family: family.as_ref().unwrap().unevaluate_in(level)?,
				},
			Project { scrutinee, projection, copyability, representation } => DynamicTerm::Project {
				scrutinee: scrutinee.unevaluate_in(level)?.into(),
				projection: *projection,
				projection_copyability: copyability.as_ref().unwrap().unevaluate_in(level)?.into(),
				projection_representation: representation.as_ref().unwrap().unevaluate_in(level)?.into(),
			},
			Suc(prev) => DynamicTerm::Suc(prev.unevaluate_in(level)?.into()),
			CaseNat { scrutinee, case_nil, case_suc, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseNat {
					scrutinee: scrutinee.unevaluate_in(level)?.into(),
					case_nil: case_nil.unevaluate_in(level)?.into(),
					case_suc: case_suc.unevaluate_in(level)?,
					fiber_copyability: fiber_copyability.unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.unevaluate_in(level)?.into(),
					motive: motive.unevaluate_in(level)?,
				},
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseEnum {
					scrutinee: scrutinee.unevaluate_in(level)?.into(),
					cases: cases.into_iter().map(|case| case.unevaluate_in(level)).collect::<Result<_, _>>()?,
					fiber_copyability: fiber_copyability.unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.unevaluate_in(level)?.into(),
					motive: motive.unevaluate_in(level)?,
				},
			Unwrap { scrutinee, copyability, representation } => DynamicTerm::Unwrap {
				scrutinee: scrutinee.unevaluate_in(level)?.into(),
				copyability: copyability.unevaluate_in(level)?.into(),
				representation: representation.unevaluate_in(level)?.into(),
			},
			UnRc { scrutinee, copyability, representation } => DynamicTerm::UnRc {
				scrutinee: scrutinee.unevaluate_in(level)?.into(),
				copyability: copyability.unevaluate_in(level)?.into(),
				representation: representation.unevaluate_in(level)?.into(),
			},
		})
	}
}

impl Unevaluate for DynamicValue {
	type Term = DynamicTerm;
	fn unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use DynamicValue::*;
		Ok(match self {
			Neutral(neutral) => neutral.unevaluate_in(level)?,
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: copyability.unevaluate_in(level)?.into(),
				representation: representation.unevaluate_in(level)?.into(),
			},
			IndexedProduct {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				base_copyability: base_copyability.unevaluate_in(level)?.into(),
				base_representation: base_representation.unevaluate_in(level)?.into(),
				base: base.unevaluate_in(level)?.into(),
				family_copyability: base_copyability.unevaluate_in(level)?.into(),
				family_representation: base_representation.unevaluate_in(level)?.into(),
				family: family.unevaluate_in(level)?,
			},
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unevaluate_in(level)?.into(),
				family: family.unevaluate_in(level)?.into(),
				body: body.unevaluate_in(level)?.into(),
			},
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Sigma {
				base_copyability: base_copyability.unevaluate_in(level)?.into(),
				base_representation: base_representation.unevaluate_in(level)?.into(),
				base: base.unevaluate_in(level)?.into(),
				family_copyability: base_copyability.unevaluate_in(level)?.into(),
				family_representation: base_representation.unevaluate_in(level)?.into(),
				family: family.unevaluate_in(level)?,
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: basepoint.unevaluate_in(level)?.into(),
				fiberpoint: fiberpoint.unevaluate_in(level)?.into(),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),
			WrapType { inner, copyability, representation } => DynamicTerm::WrapType {
				inner: inner.unevaluate_in(level)?.into(),
				copyability: copyability.unevaluate_in(level)?.into(),
				representation: representation.unevaluate_in(level)?.into(),
			},
			WrapNew(x) => DynamicTerm::WrapNew(x.unevaluate_in(level)?.into()),
			RcType { inner, copyability, representation } => DynamicTerm::RcType {
				inner: inner.unevaluate_in(level)?.into(),
				copyability: copyability.unevaluate_in(level)?.into(),
				representation: representation.unevaluate_in(level)?.into(),
			},
			RcNew(x) => DynamicTerm::RcNew(x.unevaluate_in(level)?.into()),
		})
	}
}
