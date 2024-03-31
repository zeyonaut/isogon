use super::super::ir::presyntax::Preterm;
use crate::delta::{
	common::{AnyBinder, Binder},
	ir::{
		presyntax::{Constructor, Former, Pattern, Projector, PurePreterm},
		syntax::{DynamicTerm, StaticTerm},
	},
};

pub trait Unelaborate {
	type Pre;
	fn unelaborate(self) -> Self::Pre;
}

impl Unelaborate for StaticTerm {
	type Pre = PurePreterm;
	fn unelaborate(self) -> Self::Pre {
		PurePreterm(match self {
			StaticTerm::Variable(name, _) => Preterm::Variable(name.unwrap()),

			StaticTerm::Let { grade, ty, argument, tail } => Preterm::Let {
				grade,
				ty: ty.unelaborate().into(),
				argument: argument.unelaborate().into(),
				tail: tail.unelaborate(),
			},

			StaticTerm::Universe => Preterm::Former(Former::Universe, vec![]),

			StaticTerm::Cpy => Preterm::Former(Former::Copy, vec![]),
			StaticTerm::CpyValue(c) => Preterm::Constructor(Constructor::Cpy(c), vec![]),
			StaticTerm::CpyMax(a, b) =>
				Preterm::Constructor(Constructor::CpyMax, vec![a.unelaborate(), b.unelaborate()]),

			StaticTerm::Repr => Preterm::Former(Former::Repr, vec![]),
			StaticTerm::ReprAtom(a) => Preterm::Constructor(Constructor::ReprAtom(a), vec![]),
			StaticTerm::ReprExp(n, r) => Preterm::Constructor(Constructor::ReprExp(n), vec![r.unelaborate()]),
			StaticTerm::ReprPair(a, b) =>
				Preterm::Constructor(Constructor::ReprPair, vec![a.unelaborate(), b.unelaborate()]),

			StaticTerm::Lift { liftee, copy: _, repr: _ } =>
				Preterm::Former(Former::Lift, vec![liftee.unelaborate()]),
			StaticTerm::Quote(q) => Preterm::SwitchLevel(q.unelaborate().into()),

			StaticTerm::Exp(n, t) => Preterm::Former(Former::Exp(n), vec![t.unelaborate()]),
			StaticTerm::Repeat(n, e) => Preterm::Constructor(Constructor::Exp(n), vec![e.unelaborate()]),
			StaticTerm::LetExp { grade, grade_argument, argument, tail } => Preterm::LetExp {
				grade,
				grade_argument,
				argument: argument.unelaborate().into(),
				tail: tail.unelaborate(),
			},

			StaticTerm::Pi(grade, base, family) =>
				Preterm::Pi { grade, base: base.unelaborate().into(), family: family.unelaborate().into() },
			StaticTerm::Function(grade, function) =>
				Preterm::Lambda { grade, body: function.unelaborate().into() },
			StaticTerm::Apply { scrutinee, argument } =>
				Preterm::Call { callee: scrutinee.unelaborate().into(), argument: argument.unelaborate().into() },

			StaticTerm::Sg(base, family) =>
				Preterm::Sg { base: base.unelaborate().into(), family: family.unelaborate().into() },
			StaticTerm::Pair { basepoint, fiberpoint } => Preterm::Pair {
				basepoint: basepoint.unelaborate().into(),
				fiberpoint: fiberpoint.unelaborate().into(),
			},
			StaticTerm::SgLet { grade, argument, tail } =>
				Preterm::SgLet { grade, argument: argument.unelaborate().into(), tail: tail.unelaborate() },
			StaticTerm::SgField(s, f) => Preterm::Project(s.unelaborate().into(), Projector::Field(f)),

			StaticTerm::Enum(n) => Preterm::Former(Former::Enum(n), vec![]),
			StaticTerm::EnumValue(k, v) => Preterm::Constructor(Constructor::Enum(k, v), vec![]),
			StaticTerm::CaseEnum { scrutinee, motive, cases } => {
				let card = cases.len() as u16;
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					motive: AnyBinder::from(motive).unelaborate(),
					cases: cases
						.into_iter()
						.enumerate()
						.map(|(i, e)| {
							(Pattern::Construction(Constructor::Enum(card, i as _), vec![]), e.unelaborate())
						})
						.collect(),
				}
			}
		})
	}
}

impl Unelaborate for DynamicTerm {
	type Pre = PurePreterm;
	fn unelaborate(self) -> Self::Pre {
		PurePreterm(match self {
			DynamicTerm::Variable(name, _) => Preterm::Variable(name.unwrap()),

			DynamicTerm::Let { grade, ty, argument, tail } => Preterm::Let {
				grade,
				ty: ty.unelaborate().into(),
				argument: argument.unelaborate().into(),
				tail: tail.unelaborate(),
			},

			DynamicTerm::Universe { copyability, representation } =>
				Preterm::Former(Former::Universe, vec![copyability.unelaborate(), representation.unelaborate()]),

			DynamicTerm::Splice(s) => Preterm::SwitchLevel(s.unelaborate().into()),

			DynamicTerm::Exp(n, t) => Preterm::Former(Former::Exp(n), vec![t.unelaborate()]),
			DynamicTerm::Repeat(n, e) => Preterm::Constructor(Constructor::Exp(n), vec![e.unelaborate()]),
			DynamicTerm::LetExp { grade, grade_argument, argument, tail } => Preterm::LetExp {
				grade,
				grade_argument,
				argument: argument.unelaborate().into(),
				tail: tail.unelaborate(),
			},

			DynamicTerm::Pi {
				grade,
				base_copyability: _,
				base_representation: _,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => Preterm::Pi { grade, base: base.unelaborate().into(), family: family.unelaborate().into() },
			DynamicTerm::Function { grade, base: _, family: _, body } =>
				Preterm::Lambda { grade, body: body.unelaborate().into() },
			DynamicTerm::Apply {
				scrutinee,
				argument,
				fiber_copyability: _,
				fiber_representation: _,
				base: _,
				family: _,
			} =>
				Preterm::Call { callee: scrutinee.unelaborate().into(), argument: argument.unelaborate().into() },

			DynamicTerm::Sg { base_copy: _, base_repr: _, base, family_copy: _, family_repr: _, family } =>
				Preterm::Sg { base: base.unelaborate().into(), family: family.unelaborate().into() },
			DynamicTerm::Pair { basepoint, fiberpoint } => Preterm::Pair {
				basepoint: basepoint.unelaborate().into(),
				fiberpoint: fiberpoint.unelaborate().into(),
			},
			DynamicTerm::SgLet { grade, argument, tail } =>
				Preterm::SgLet { grade, argument: argument.unelaborate().into(), tail: tail.unelaborate() },
			DynamicTerm::SgField { scrutinee, field } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Field(field)),

			DynamicTerm::Enum(n) => Preterm::Former(Former::Enum(n), vec![]),
			DynamicTerm::EnumValue(k, v) => Preterm::Constructor(Constructor::Enum(k, v), vec![]),
			DynamicTerm::CaseEnum {
				scrutinee,
				cases,
				fiber_copyability: _,
				fiber_representation: _,
				motive,
			} => {
				let card = cases.len() as u16;
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					motive: AnyBinder::from(motive).unelaborate(),
					cases: cases
						.into_iter()
						.enumerate()
						.map(|(i, e)| {
							(Pattern::Construction(Constructor::Enum(card, i as _), vec![]), e.unelaborate())
						})
						.collect(),
				}
			}

			DynamicTerm::Id { copy: _, repr: _, space, left, right } =>
				Preterm::Former(Former::Id, vec![space.unelaborate(), left.unelaborate(), right.unelaborate()]),
			DynamicTerm::Refl => Preterm::Constructor(Constructor::Refl, vec![]),
			DynamicTerm::CasePath { scrutinee, motive, case_refl } => Preterm::Split {
				scrutinee: scrutinee.unelaborate().into(),
				motive: AnyBinder::from(motive).unelaborate(),
				cases: vec![(Pattern::Construction(Constructor::Refl, vec![]), case_refl.unelaborate())],
			},

			DynamicTerm::Bx { inner, copy: _, repr: _ } =>
				Preterm::Former(Former::Bx, vec![inner.unelaborate()]),
			DynamicTerm::BxValue(v) => Preterm::Constructor(Constructor::Bx, vec![v.unelaborate()]),
			DynamicTerm::BxProject { scrutinee, copy: _, repr: _ } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Bx),

			DynamicTerm::Wrap { inner, copy: _, repr: _ } =>
				Preterm::Former(Former::Wrap, vec![inner.unelaborate()]),
			DynamicTerm::WrapValue(v) => Preterm::Constructor(Constructor::Wrap, vec![v.unelaborate()]),
			DynamicTerm::WrapProject { scrutinee, copy: _, repr: _ } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Wrap),
		})
	}
}

impl<const N: usize, T: Unelaborate> Unelaborate for Binder<Box<T>, N> {
	type Pre = Binder<Box<T::Pre>, N>;
	fn unelaborate(self) -> Self::Pre { Binder::new(self.parameters, self.body.unelaborate().into()) }
}

impl<T: Unelaborate> Unelaborate for AnyBinder<Box<T>> {
	type Pre = AnyBinder<Box<T::Pre>>;
	fn unelaborate(self) -> Self::Pre { AnyBinder::new(self.parameters, self.body.unelaborate().into()) }
}
