use super::stage::StageAuto;
use crate::delta::{
	common::{bind, Binder, Closure, Cpy, Index, Label, Level, UniverseKind},
	ir::{
		object::{DynamicValue, Environment},
		syntax::{DynamicTerm, KindTerm, StaticTerm},
	},
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

	fn unstage_in(&self, level: Level) -> Self::CoreTerm;
}

impl Unstage for DynamicValue {
	type CoreTerm = DynamicTerm;
	fn unstage_in(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use DynamicValue::*;
		match self {
			// Variables.
			Variable(name, v) => DynamicTerm::Variable(*name, Index(context_len - (v.0 + 1))),

			// Let-expressions.
			Let { grade, ty_kind, ty, argument, tail } => DynamicTerm::Let {
				grade: *grade,
				ty: ty.unstage_in(level).into(),
				argument_kind: ty_kind.unstage_in(level).into(),
				argument: argument.unstage_in(level).into(),
				tail: tail.unstage_in(level),
			},

			// Types.
			Universe(kind) => DynamicTerm::Universe { kind: kind.unstage_in(level).into() },

			// Repeated programs.
			Exp(n, kind, t) => DynamicTerm::Exp(*n, kind.unstage_in(level).into(), t.unstage_in(level).into()),
			Repeat(n, t) => DynamicTerm::Repeat(*n, t.unstage_in(level).into()),
			ExpLet { grade, grade_argument, argument, kind, tail } => DynamicTerm::ExpLet {
				grade: *grade,
				grade_argument: *grade_argument,
				argument: argument.unstage_in(level).into(),
				kind: kind.unstage_in(level).into(),
				tail: tail.unstage_in(level),
			},
			ExpProject(t) => DynamicTerm::ExpProject(t.unstage_in(level).into()),

			// Dependent functions.
			Pi { grade, base_kind, base, family_kind, family } => DynamicTerm::Pi {
				grade: *grade,
				base_kind: base_kind.unstage_in(level).into(),
				base: base.unstage_in(level).into(),
				family_kind: family_kind.unstage_in(level).into(),
				family: family.unstage_in(level),
			},
			Function { grade, body, domain_kind, codomain_kind } => DynamicTerm::Function {
				grade: *grade,
				body: body.unstage_in(level),
				domain_kind: domain_kind.as_ref().map(|kind| kind.unstage_in(level).into()),
				codomain_kind: codomain_kind.as_ref().map(|kind| kind.unstage_in(level).into()),
			},
			Apply { scrutinee, grade, argument, family_kind } => DynamicTerm::Apply {
				scrutinee: scrutinee.unstage_in(level).into(),
				grade: *grade,
				argument: argument.unstage_in(level).into(),
				family_kind: family_kind.as_ref().map(|kind| kind.unstage_in(level).into()),
			},

			// Dependent pairs.
			Sg { base_kind, base, family_kind, family } => DynamicTerm::Sg {
				base_kind: base_kind.unstage_in(level).into(),
				base: base.unstage_in(level).into(),
				family_kind: family_kind.unstage_in(level).into(),
				family: family.unstage_in(level),
			},
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: basepoint.unstage_in(level).into(),
				fiberpoint: fiberpoint.unstage_in(level).into(),
			},
			SgLet { grade, argument, kinds, tail } => DynamicTerm::SgLet {
				grade: *grade,
				argument: argument.unstage_in(level).into(),
				kinds: kinds.each_ref().map(|kind| kind.unstage_in(level).into()),
				tail: tail.unstage_in(level),
			},
			SgField(scrutinee, field) =>
				DynamicTerm::SgField { scrutinee: scrutinee.unstage_in(level).into(), field: *field },

			// Enumerated numbers.
			Enum(k) => DynamicTerm::Enum(*k),
			EnumValue(k, v) => DynamicTerm::EnumValue(*k, *v),
			CaseEnum { scrutinee, cases, motive_kind, motive } => DynamicTerm::CaseEnum {
				scrutinee: scrutinee.unstage_in(level).into(),
				cases: cases.iter().map(|case| case.unstage_in(level)).collect(),
				motive_kind: motive_kind.as_ref().map(|kind| kind.unstage_in(level).into()),
				motive: motive.unstage_in(level),
			},

			// Paths.
			Id { kind, space, left, right } => DynamicTerm::Id {
				kind: kind.unstage_in(level).into(),
				space: space.unstage_in(level).into(),
				left: left.unstage_in(level).into(),
				right: right.unstage_in(level).into(),
			},
			Refl => DynamicTerm::Refl,
			CasePath { scrutinee, motive, case_refl } => DynamicTerm::CasePath {
				scrutinee: scrutinee.unstage_in(level).into(),
				motive: motive.unstage_in(level),
				case_refl: case_refl.unstage_in(level).into(),
			},

			// Natural numbers.
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Suc(prev) => DynamicTerm::Suc(prev.unstage_in(level).into()),
			CaseNat { scrutinee, case_nil, case_suc, motive_kind, motive } => DynamicTerm::CaseNat {
				scrutinee: scrutinee.unstage_in(level).into(),
				motive_kind: motive_kind.as_ref().map(|kind| kind.unstage_in(level).into()),
				motive: motive.unstage_in(level),
				case_nil: case_nil.unstage_in(level).into(),
				case_suc: case_suc.unstage_in(level),
			},

			// Wrappers.
			Bx(inner, kind) =>
				DynamicTerm::Bx { inner: inner.unstage_in(level).into(), kind: kind.unstage_in(level).into() },
			BxValue(x) => DynamicTerm::BxValue(x.unstage_in(level).into()),
			BxProject(scrutinee, kind) => DynamicTerm::BxProject {
				scrutinee: scrutinee.unstage_in(level).into(),
				kind: kind.as_ref().map(|kind| kind.unstage_in(level).into()),
			},

			Wrap(inner, kind) =>
				DynamicTerm::Bx { inner: inner.unstage_in(level).into(), kind: kind.unstage_in(level).into() },
			WrapValue(x) => DynamicTerm::WrapValue(x.unstage_in(level).into()),
			WrapProject(scrutinee, kind) => DynamicTerm::BxProject {
				scrutinee: scrutinee.unstage_in(level).into(),
				kind: kind.as_ref().map(|kind| kind.unstage_in(level).into()),
			},
		}
	}
}

impl Unstage for UniverseKind {
	type CoreTerm = KindTerm;
	fn unstage_in(&self, _: Level) -> Self::CoreTerm {
		KindTerm {
			copy: match self.copy {
				Cpy::Tr => StaticTerm::CpyMax(vec![]),
				Cpy::Nt => StaticTerm::CpyNt,
			},
			repr: StaticTerm::from(self.repr.as_ref()),
		}
	}
}
impl<const N: usize> Unstage for Closure<Environment, DynamicTerm, N> {
	type CoreTerm = Binder<Label, Box<DynamicTerm>, N>;
	fn unstage_in(&self, level: Level) -> Self::CoreTerm {
		bind(self.parameters, self.stage_auto(level).unstage_in(level + N))
	}
}
