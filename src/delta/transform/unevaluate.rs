use super::autolyze::Autolyze;
use crate::delta::{
	common::{bind, Binder, Closure, Index, Level},
	ir::{
		semantics::{DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue},
		syntax::{DynamicTerm, StaticTerm},
	},
};

pub trait Unevaluate {
	type Term;
	/// Transforms a value into a core term.
	fn unevaluate(&self) -> Self::Term { self.unevaluate_in(Level(0)) }

	#[must_use]
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()>;

	fn unevaluate_in(&self, level: Level) -> Self::Term { self.try_unevaluate_in(level).unwrap() }
}

impl<const N: usize> Unevaluate for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(bind(self.parameters, self.autolyze(level).try_unevaluate_in(level + N)?))
	}
}

impl<const N: usize> Unevaluate for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(bind(self.parameters, self.autolyze(level).try_unevaluate_in(level + N)?))
	}
}

impl Unevaluate for StaticNeutral {
	type Term = StaticTerm;
	fn try_unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use StaticNeutral::*;
		Ok(match self {
			Variable(name, Level(level)) =>
				StaticTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),
			MaxCopyability(a, b) =>
				StaticTerm::MaxCopyability(a.try_unevaluate_in(level)?.into(), b.try_unevaluate_in(level)?.into()),
			Apply(callee, argument) => StaticTerm::Apply {
				scrutinee: callee.try_unevaluate_in(level)?.into(),
				argument: argument.try_unevaluate_in(level)?.into(),
			},
			LetExp { scrutinee, grade, tail } => StaticTerm::LetExp  { argument: scrutinee.unevaluate_in(level).into(), grade: *grade, tail: tail.unevaluate_in(level) },
		})
	}
}

impl Unevaluate for StaticValue {
	type Term = StaticTerm;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use StaticValue::*;
		Ok(match self {
			Neutral(neutral) => neutral.try_unevaluate_in(level)?,
			Universe => StaticTerm::Universe,
			IndexedProduct(grade, base, family) =>
				StaticTerm::Pi(*grade, base.try_unevaluate_in(level)?.into(), family.try_unevaluate_in(level)?),
			Function(grade, function) => StaticTerm::Lambda(*grade, function.try_unevaluate_in(level)?),
			Lift { ty: liftee, copy, repr } => StaticTerm::Lift {
				liftee: liftee.try_unevaluate_in(level)?.into(),
				copy: copy.try_unevaluate_in(level)?.into(),
				repr: repr.try_unevaluate_in(level)?.into(),
			},
			Quote(quotee) => StaticTerm::Quote(quotee.try_unevaluate_in(level)?.into()),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprExp(grade, r) => StaticTerm::ReprExp(*grade, r.unevaluate_in(level).into()),
			Repeat(grade, value) => StaticTerm::Repeat(*grade, value.unevaluate_in(level).into()),
			Exp(grade, ty) => StaticTerm::Exp(*grade, ty.unevaluate_in(level).into()),
		})
	}
}

impl Unevaluate for DynamicNeutral {
	type Term = DynamicTerm;
	fn try_unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use DynamicNeutral::*;
		Ok(match self {
			Variable(name, Level(level)) =>
				DynamicTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),
			Splice(splicee) => DynamicTerm::Splice(splicee.try_unevaluate_in(level)?.into()),
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicTerm::Apply {
					scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
					argument: argument.try_unevaluate_in(level)?.into(),
					fiber_copyability: fiber_copyability.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					base: base.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					family: family.as_ref().unwrap().try_unevaluate_in(level)?,
				},
					 LetExp { scrutinee, grade, tail } => DynamicTerm::LetExp  { argument: scrutinee.unevaluate_in(level).into(), grade: *grade, tail: tail.unevaluate_in(level) },
		})
	}
}

impl Unevaluate for DynamicValue {
	type Term = DynamicTerm;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use DynamicValue::*;
		Ok(match self {
			Neutral(neutral) => neutral.try_unevaluate_in(level)?,
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: copyability.try_unevaluate_in(level)?.into(),
				representation: representation.try_unevaluate_in(level)?.into(),
			},
			IndexedProduct {
				grade,
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				grade: *grade,
				base_copyability: base_copyability.try_unevaluate_in(level)?.into(),
				base_representation: base_representation.try_unevaluate_in(level)?.into(),
				base: base.try_unevaluate_in(level)?.into(),
				family_copyability: base_copyability.try_unevaluate_in(level)?.into(),
				family_representation: base_representation.try_unevaluate_in(level)?.into(),
				family: family.try_unevaluate_in(level)?,
			},
			Function { grade, base, family, body } => DynamicTerm::Function {
				grade: *grade,
				base: base.try_unevaluate_in(level)?.into(),
				family: family.try_unevaluate_in(level)?.into(),
				body: body.try_unevaluate_in(level)?.into(),
			},
			Repeat(grade, value) => DynamicTerm::Repeat(*grade, value.unevaluate_in(level).into()),
			Exp(grade, ty) => DynamicTerm::Exp(*grade, ty.unevaluate_in(level).into()),
		})
	}
}