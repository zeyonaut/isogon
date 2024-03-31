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

impl Unevaluate for StaticValue {
	type Term = StaticTerm;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use StaticValue::*;
		Ok(match self {
			// Neutrals.
			Neutral(neutral) => neutral.try_unevaluate_in(level)?,

			// Types.
			Universe => StaticTerm::Universe,

			// Universe indices.
			Cpy => StaticTerm::Cpy,
			CpyValue(c) => StaticTerm::CpyValue(*c),

			ReprType => StaticTerm::Repr,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(l, r) => StaticTerm::ReprPair(l.unevaluate_in(level).into(), r.unevaluate_in(level).into()),
			ReprExp(grade, r) => StaticTerm::ReprExp(*grade, r.unevaluate_in(level).into()),

			// Quoted programs.
			Lift { ty: liftee, copy, repr } => StaticTerm::Lift {
				liftee: liftee.try_unevaluate_in(level)?.into(),
				copy: copy.try_unevaluate_in(level)?.into(),
				repr: repr.try_unevaluate_in(level)?.into(),
			},
			Quote(quotee) => StaticTerm::Quote(quotee.try_unevaluate_in(level)?.into()),

			// Repeated programs.
			Exp(grade, ty) => StaticTerm::Exp(*grade, ty.unevaluate_in(level).into()),
			Repeat(grade, value) => StaticTerm::Repeat(*grade, value.unevaluate_in(level).into()),

			// Dependent functions.
			IndexedProduct(grade, base, family) =>
				StaticTerm::Pi(*grade, base.try_unevaluate_in(level)?.into(), family.try_unevaluate_in(level)?),
			Function(grade, function) => StaticTerm::Function(*grade, function.try_unevaluate_in(level)?),

			// Dependent pairs.
			IndexedSum(base, family) =>
				StaticTerm::Sg(base.try_unevaluate_in(level)?.into(), family.try_unevaluate_in(level)?),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: basepoint.try_unevaluate_in(level)?.into(),
				fiberpoint: fiberpoint.try_unevaluate_in(level)?.into(),
			},

			// Enumerated values.
			Enum(k) => StaticTerm::Enum(*k),
			EnumValue(k, v) => StaticTerm::EnumValue(*k, *v),
		})
	}
}

impl Unevaluate for StaticNeutral {
	type Term = StaticTerm;
	fn try_unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use StaticNeutral::*;
		Ok(match self {
			// Variables.
			Variable(name, Level(level)) =>
				StaticTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),

			// Universe indices.
			CpyMax(a, b) =>
				StaticTerm::CpyMax(a.try_unevaluate_in(level)?.into(), b.try_unevaluate_in(level)?.into()),

			// Repeated programs.
			LetExp { scrutinee, grade, tail } => StaticTerm::LetExp {
				argument: scrutinee.unevaluate_in(level).into(),
				grade: *grade,
				// NOTE: It seems like we're converging towards not having LetExp in the domain at all!
				// So, we'll probably just remove it instead of implement it.
				grade_argument: unimplemented!(),
				tail: tail.unevaluate_in(level),
			},

			// Dependent functions.
			Apply(callee, argument) => StaticTerm::Apply {
				scrutinee: callee.try_unevaluate_in(level)?.into(),
				argument: argument.try_unevaluate_in(level)?.into(),
			},

			// Dependent pairs.
			Project(scrutinee, projection) =>
				StaticTerm::SgField(scrutinee.try_unevaluate_in(level)?.into(), *projection),

			// Enumerated numbers.
			CaseEnum { scrutinee, motive, cases } => StaticTerm::CaseEnum {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive: motive.try_unevaluate_in(level)?,
				cases: cases.into_iter().map(|case| case.try_unevaluate_in(level)).collect::<Result<_, _>>()?,
			},
		})
	}
}

impl Unevaluate for DynamicValue {
	type Term = DynamicTerm;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		use DynamicValue::*;
		Ok(match self {
			// Neutrals.
			Neutral(neutral) => neutral.try_unevaluate_in(level)?,

			// Types.
			Universe { copy: copyability, repr: representation } => DynamicTerm::Universe {
				copyability: copyability.try_unevaluate_in(level)?.into(),
				representation: representation.try_unevaluate_in(level)?.into(),
			},

			// Repeated programs.
			Exp(grade, ty) => DynamicTerm::Exp(*grade, ty.unevaluate_in(level).into()),
			Repeat(grade, value) => DynamicTerm::Repeat(*grade, value.unevaluate_in(level).into()),

			// Dependent functions.
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

			// Dependent pairs.
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicTerm::Sg {
				base_copy: base_copyability.try_unevaluate_in(level)?.into(),
				base_repr: base_representation.try_unevaluate_in(level)?.into(),
				base: base.try_unevaluate_in(level)?.into(),
				family_copy: family_copyability.try_unevaluate_in(level)?.into(),
				family_repr: family_representation.try_unevaluate_in(level)?.into(),
				family: family.try_unevaluate_in(level)?,
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: basepoint.try_unevaluate_in(level)?.into(),
				fiberpoint: fiberpoint.try_unevaluate_in(level)?.into(),
			},

			// Enumerated numbers.
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),

			// Paths.
			Id { copy, repr, space, left, right } => DynamicTerm::Id {
				copy: copy.try_unevaluate_in(level)?.into(),
				repr: repr.try_unevaluate_in(level)?.into(),
				space: space.try_unevaluate_in(level)?.into(),
				left: left.try_unevaluate_in(level)?.into(),
				right: right.try_unevaluate_in(level)?.into(),
			},
			Refl => DynamicTerm::Refl,

			// Wrappers.
			Bx { inner, copy: copyability, repr: representation } => DynamicTerm::Bx {
				inner: inner.try_unevaluate_in(level)?.into(),
				copy: copyability.try_unevaluate_in(level)?.into(),
				repr: representation.try_unevaluate_in(level)?.into(),
			},
			BxValue(x) => DynamicTerm::BxValue(x.try_unevaluate_in(level)?.into()),
			Wrap { inner, copy: copyability, repr: representation } => DynamicTerm::Wrap {
				inner: inner.try_unevaluate_in(level)?.into(),
				copy: copyability.try_unevaluate_in(level)?.into(),
				repr: representation.try_unevaluate_in(level)?.into(),
			},
			WrapValue(x) => DynamicTerm::WrapValue(x.try_unevaluate_in(level)?.into()),
		})
	}
}

impl Unevaluate for DynamicNeutral {
	type Term = DynamicTerm;
	fn try_unevaluate_in(&self, level @ Level(context_length): Level) -> Result<Self::Term, ()> {
		use DynamicNeutral::*;
		Ok(match self {
			// Variables.
			Variable(name, Level(level)) =>
				DynamicTerm::Variable(*name, Index(context_length.checked_sub(level + 1).ok_or(())?)),

			// Quoted programs.
			Splice(splicee) => DynamicTerm::Splice(splicee.try_unevaluate_in(level)?.into()),

			// Repeated programs.
			LetExp { scrutinee, grade, tail } => DynamicTerm::LetExp {
				argument: scrutinee.unevaluate_in(level).into(),
				grade: *grade,
				grade_argument: unimplemented!(),
				tail: tail.unevaluate_in(level),
			},

			// Dependent functions.
			Apply { scrutinee, argument, fiber_copyability, fiber_representation, base, family } =>
				DynamicTerm::Apply {
					scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
					argument: argument.try_unevaluate_in(level)?.into(),
					fiber_copyability: fiber_copyability.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					base: base.as_ref().unwrap().try_unevaluate_in(level)?.into(),
					family: family.as_ref().unwrap().try_unevaluate_in(level)?,
				},

			// Dependent pairs.
			Project { scrutinee, projection } =>
				DynamicTerm::SgField { scrutinee: scrutinee.try_unevaluate_in(level)?.into(), field: *projection },

			// Enumerated numbers.
			CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } =>
				DynamicTerm::CaseEnum {
					scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
					cases: cases
						.into_iter()
						.map(|case| case.try_unevaluate_in(level))
						.collect::<Result<_, _>>()?,
					fiber_copyability: fiber_copyability.try_unevaluate_in(level)?.into(),
					fiber_representation: fiber_representation.try_unevaluate_in(level)?.into(),
					motive: motive.try_unevaluate_in(level)?,
				},

			// Paths.
			CasePath { scrutinee, motive, case_refl } => DynamicTerm::CasePath {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive: motive.try_unevaluate_in(level)?,
				case_refl: case_refl.try_unevaluate_in(level)?.into(),
			},

			// Wrappers.
			BxProject { scrutinee, copyability, representation } => DynamicTerm::BxProject {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				copy: copyability.try_unevaluate_in(level)?.into(),
				repr: representation.try_unevaluate_in(level)?.into(),
			},
			WrapProject { scrutinee, copyability, representation } => DynamicTerm::WrapProject {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				copy: copyability.try_unevaluate_in(level)?.into(),
				repr: representation.try_unevaluate_in(level)?.into(),
			},
		})
	}
}
