use super::evaluate::EvaluateAuto;
use crate::delta::{
	common::{bind, Binder, Closure, Index, Level},
	ir::{
		semantics::{DynamicNeutral, DynamicValue, Environment, KindValue, StaticNeutral, StaticValue},
		syntax::{DynamicTerm, KindTerm, StaticTerm},
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
		Ok(bind(self.parameters, self.evaluate_auto(level).try_unevaluate_in(level + N)?))
	}
}

impl<const N: usize> Unevaluate for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(bind(self.parameters, self.evaluate_auto(level).try_unevaluate_in(level + N)?))
	}
}

impl Unevaluate for KindValue {
	type Term = KindTerm;
	fn try_unevaluate_in(&self, level: Level) -> Result<Self::Term, ()> {
		Ok(KindTerm { copy: self.copy.unevaluate_in(level), repr: self.repr.unevaluate_in(level) })
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
			Lift { ty: liftee, kind } => StaticTerm::Lift {
				liftee: liftee.try_unevaluate_in(level)?.into(),
				kind: kind.try_unevaluate_in(level)?.into(),
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

			// Natural numbers.
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
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
			ExpProject(_) => unimplemented!(),

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

			// Natural numbers.
			Suc(prev) => StaticTerm::Suc(prev.try_unevaluate_in(level)?.into()),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive: motive.try_unevaluate_in(level)?,
				case_nil: case_nil.try_unevaluate_in(level)?.into(),
				case_suc: case_suc.try_unevaluate_in(level)?,
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
			Universe { kind } => DynamicTerm::Universe { kind: kind.try_unevaluate_in(level)?.into() },

			// Repeated programs.
			Exp(grade, ty) => DynamicTerm::Exp(*grade, ty.unevaluate_in(level).into()),
			Repeat(grade, value) => DynamicTerm::Repeat(*grade, value.unevaluate_in(level).into()),

			// Dependent functions.
			IndexedProduct { grade, base_kind, base, family_kind, family } => DynamicTerm::Pi {
				grade: *grade,
				base_kind: base_kind.try_unevaluate_in(level)?.into(),
				base: base.try_unevaluate_in(level)?.into(),
				family_kind: family_kind.try_unevaluate_in(level)?.into(),
				family: family.try_unevaluate_in(level)?,
			},
			Function { grade, body } =>
				DynamicTerm::Function { grade: *grade, body: body.try_unevaluate_in(level)?.into() },

			// Dependent pairs.
			IndexedSum { base_kind, base, family_kind, family } => DynamicTerm::Sg {
				base_kind: base_kind.try_unevaluate_in(level)?.into(),
				base: base.try_unevaluate_in(level)?.into(),
				family_kind: family_kind.try_unevaluate_in(level)?.into(),
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
			Id { kind, space, left, right } => DynamicTerm::Id {
				kind: kind.try_unevaluate_in(level)?.into(),
				space: space.try_unevaluate_in(level)?.into(),
				left: left.try_unevaluate_in(level)?.into(),
				right: right.try_unevaluate_in(level)?.into(),
			},
			Refl => DynamicTerm::Refl,

			// Natural numbers.
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),

			// Wrappers.
			Bx { kind, inner } => DynamicTerm::Bx {
				kind: kind.try_unevaluate_in(level)?.into(),
				inner: inner.try_unevaluate_in(level)?.into(),
			},
			BxValue(x) => DynamicTerm::BxValue(x.try_unevaluate_in(level)?.into()),
			Wrap { kind, inner } => DynamicTerm::Wrap {
				kind: kind.try_unevaluate_in(level)?.into(),
				inner: inner.try_unevaluate_in(level)?.into(),
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
			ExpProject(scrutinee) => unimplemented!(),

			// Dependent functions.
			Apply { scrutinee, argument } => DynamicTerm::Apply {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				argument: argument.try_unevaluate_in(level)?.into(),
				family_kind: None,
			},

			// Dependent pairs.
			Project { scrutinee, projection } =>
				DynamicTerm::SgField { scrutinee: scrutinee.try_unevaluate_in(level)?.into(), field: *projection },

			// Enumerated numbers.
			CaseEnum { scrutinee, cases, motive } => DynamicTerm::CaseEnum {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive_kind: None,
				motive: motive.try_unevaluate_in(level)?,
				cases: cases.into_iter().map(|case| case.try_unevaluate_in(level)).collect::<Result<_, _>>()?,
			},

			// Paths.
			CasePath { scrutinee, motive, case_refl } => DynamicTerm::CasePath {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive: motive.try_unevaluate_in(level)?,
				case_refl: case_refl.try_unevaluate_in(level)?.into(),
			},

			// Natural numbers.
			Suc(prev) => DynamicTerm::Suc(prev.try_unevaluate_in(level)?.into()),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: scrutinee.try_unevaluate_in(level)?.into(),
				motive_kind: None,
				motive: motive.try_unevaluate_in(level)?,
				case_nil: case_nil.try_unevaluate_in(level)?.into(),
				case_suc: case_suc.try_unevaluate_in(level)?,
			},

			// Wrappers.
			BxProject(scrutinee) =>
				DynamicTerm::BxProject { scrutinee: scrutinee.try_unevaluate_in(level)?.into(), kind: None },
			WrapProject(scrutinee) =>
				DynamicTerm::WrapProject { scrutinee: scrutinee.try_unevaluate_in(level)?.into(), kind: None },
		})
	}
}
