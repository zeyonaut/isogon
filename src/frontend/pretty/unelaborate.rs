use crate::{
	common::{AnyBinder, Binder, Cpy, Label},
	ir::{
		presyntax::{Constructor, Former, IrrefutablePattern, Pattern, Preterm, Projector, PurePreterm},
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
			StaticTerm::Variable(Some(name), _) => Preterm::Variable(name),
			StaticTerm::Variable(None, index) => Preterm::Index(index),

			StaticTerm::Let { grade, ty, argument, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: true,
					grade: Some(grade),
					tys: vec![ty.unelaborate()],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Label(tail.parameter()),
					tail: tail.body,
				}
			}

			StaticTerm::Universe(c) => Preterm::Former(
				Former::Universe,
				vec![PurePreterm(Preterm::Constructor(Constructor::Cpy(c), vec![]))],
			),

			StaticTerm::Cpy => Preterm::Former(Former::Copy, vec![]),
			StaticTerm::CpyNt => Preterm::Constructor(Constructor::Cpy(Cpy::Nt), vec![]),
			StaticTerm::CpyMax(set) => {
				let set: Vec<_> = set.into_iter().map(|x| x.unelaborate()).collect();
				if set.is_empty() {
					Preterm::Constructor(Constructor::Cpy(Cpy::Tr), vec![])
				} else if set.len() == 1 {
					let Ok(set) = <Box<[_; 1]>>::try_from(set) else {
						unreachable!();
					};
					let [set] = *set;
					set.0
				} else {
					Preterm::Constructor(Constructor::CpyMax, set)
				}
			}

			StaticTerm::Repr => Preterm::Former(Former::Repr, vec![]),
			StaticTerm::ReprAtom(a) => Preterm::Constructor(Constructor::ReprAtom(a), vec![]),
			StaticTerm::ReprExp { len, kind } => Preterm::Constructor(
				Constructor::ReprExp(len.0),
				vec![kind.copy.unelaborate(), kind.repr.unelaborate()],
			),
			StaticTerm::ReprPair(a, b) =>
				Preterm::Constructor(Constructor::ReprPair, vec![a.unelaborate(), b.unelaborate()]),

			StaticTerm::Lift { liftee, kind: _ } => Preterm::Former(Former::Lift, vec![liftee.unelaborate()]),
			StaticTerm::Quote(q) => Preterm::SwitchLevel(q.unelaborate().into()),

			StaticTerm::Exp(n, _, t) => Preterm::Former(Former::Exp(n), vec![t.unelaborate()]),
			StaticTerm::Repeat(n, e) => Preterm::Constructor(Constructor::Exp(n), vec![e.unelaborate()]),
			StaticTerm::ExpLet { grade, grade_argument, argument, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: true,
					grade: Some(grade),
					tys: vec![],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Exp(grade_argument, tail.parameter()),
					tail: tail.body,
				}
			}
			StaticTerm::ExpProject(t) => Preterm::Project(t.unelaborate().into(), Projector::Exp),

			StaticTerm::Pi { fragment, base_copy: _, base, family_copy: _, family } =>
				Preterm::Pi { fragment, base: base.unelaborate().into(), family: family.unelaborate() },
			StaticTerm::Function(_, function) => Preterm::Lambda { body: function.unelaborate() },
			StaticTerm::Apply { scrutinee, argument } =>
				Preterm::Call { callee: scrutinee.unelaborate().into(), argument: argument.unelaborate().into() },

			StaticTerm::Sg { base_copy: _, base, family_copy: _, family } =>
				Preterm::Sg { base: base.unelaborate().into(), family: family.unelaborate() },
			StaticTerm::Pair { basepoint, fiberpoint } => Preterm::Pair {
				basepoint: basepoint.unelaborate().into(),
				fiberpoint: fiberpoint.unelaborate().into(),
			},
			StaticTerm::SgLet { grade, argument, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: true,
					grade: Some(grade),
					tys: vec![],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Pair(tail.parameters),
					tail: tail.body,
				}
			}
			StaticTerm::SgField(s, f) => Preterm::Project(s.unelaborate().into(), Projector::Field(f)),

			StaticTerm::Enum(n) => Preterm::Former(Former::Enum(n), vec![]),
			StaticTerm::EnumValue(k, v) => Preterm::Constructor(Constructor::Enum(k, v), vec![]),
			StaticTerm::CaseEnum { scrutinee, motive, cases } => {
				let card = cases.len() as u16;
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					is_cast: false,
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

			StaticTerm::Nat => Preterm::Former(Former::Nat, vec![]),
			StaticTerm::Num(n) => Preterm::Constructor(Constructor::Num(n), vec![]),
			StaticTerm::Suc(n) => Preterm::Constructor(Constructor::Suc, vec![n.unelaborate()]),
			StaticTerm::CaseNat { scrutinee, motive, case_nil, case_suc } => {
				let case_suc = case_suc.unelaborate();
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					is_cast: false,
					motive: AnyBinder::from(motive).unelaborate(),
					cases: vec![
						(Pattern::Construction(Constructor::Num(0), vec![]), case_nil.unelaborate()),
						(
							Pattern::Construction(
								Constructor::Suc,
								vec![Pattern::Witness {
									index: case_suc.parameters[0],
									witness: case_suc.parameters[1],
								}],
							),
							*case_suc.body,
						),
					],
				}
			}
		})
	}
}

impl Unelaborate for DynamicTerm {
	type Pre = PurePreterm;
	fn unelaborate(self) -> Self::Pre {
		PurePreterm(match self {
			DynamicTerm::Variable(Some(name), _) => Preterm::Variable(name),
			DynamicTerm::Variable(None, index) => Preterm::Index(index),

			DynamicTerm::Def { grade, ty, argument, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: true,
					grade: Some(grade),
					tys: vec![ty.unelaborate()],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Label(tail.parameter()),
					tail: tail.body,
				}
			}
			DynamicTerm::Let { grade, ty, argument_kind: _, argument, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: false,
					grade: Some(grade.into()),
					tys: vec![ty.unelaborate()],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Label(tail.parameter()),
					tail: tail.body,
				}
			}

			DynamicTerm::Universe { kind } =>
				Preterm::Former(Former::Universe, vec![kind.copy.unelaborate(), kind.repr.unelaborate()]),

			DynamicTerm::Splice(s) => Preterm::SwitchLevel(s.unelaborate().into()),

			DynamicTerm::Exp(n, _, t) => Preterm::Former(Former::Exp(n.into()), vec![t.unelaborate()]),
			DynamicTerm::Repeat { grade, kind: _, term } =>
				Preterm::Constructor(Constructor::Exp(grade.into()), vec![term.unelaborate()]),
			DynamicTerm::ExpLet { grade, grade_argument, argument, kind: _, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: false,
					grade: Some(grade.into()),
					tys: vec![],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Exp(grade_argument.into(), tail.parameter()),
					tail: tail.body,
				}
			}
			DynamicTerm::ExpProject(t) => Preterm::Project(t.unelaborate().into(), Projector::Exp),

			DynamicTerm::Pi { fragment, base_kind: _, base, family_kind: _, family } =>
				Preterm::Pi { fragment, base: base.unelaborate().into(), family: family.unelaborate() },
			DynamicTerm::Function { fragment: _, body, domain_kind: _, codomain_kind: _ } =>
				Preterm::Lambda { body: body.unelaborate() },
			DynamicTerm::Apply { scrutinee, fragment: _, argument, family_kind: _ } =>
				Preterm::Call { callee: scrutinee.unelaborate().into(), argument: argument.unelaborate().into() },

			DynamicTerm::Sg { base_kind: _, base, family_kind: _, family } =>
				Preterm::Sg { base: base.unelaborate().into(), family: family.unelaborate() },
			DynamicTerm::Pair { basepoint, fiberpoint } => Preterm::Pair {
				basepoint: basepoint.unelaborate().into(),
				fiberpoint: fiberpoint.unelaborate().into(),
			},
			DynamicTerm::SgLet { grade, argument, kinds: _, tail } => {
				let tail = tail.unelaborate();
				Preterm::Let {
					is_meta: false,
					grade: Some(grade.into()),
					tys: vec![],
					argument: argument.unelaborate().into(),
					pattern: IrrefutablePattern::Pair(tail.parameters),
					tail: tail.body,
				}
			}
			DynamicTerm::SgField { scrutinee, field } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Field(field)),

			DynamicTerm::Enum(n) => Preterm::Former(Former::Enum(n), vec![]),
			DynamicTerm::EnumValue(k, v) => Preterm::Constructor(Constructor::Enum(k, v), vec![]),
			DynamicTerm::CaseEnum { scrutinee, cases, motive_kind: _, motive } => {
				let card = cases.len() as u16;
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					is_cast: false,
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

			DynamicTerm::Id { kind: _, space, left, right } =>
				Preterm::Former(Former::Id, vec![space.unelaborate(), left.unelaborate(), right.unelaborate()]),
			DynamicTerm::Refl => Preterm::Constructor(Constructor::Refl, vec![]),
			DynamicTerm::CasePath { scrutinee, motive, case_refl } => Preterm::Split {
				scrutinee: scrutinee.unelaborate().into(),
				is_cast: true,
				motive: AnyBinder::from(motive).unelaborate(),
				cases: vec![(Pattern::Construction(Constructor::Refl, vec![]), case_refl.unelaborate())],
			},

			DynamicTerm::Nat => Preterm::Former(Former::Nat, vec![]),
			DynamicTerm::Num(n) => Preterm::Constructor(Constructor::Num(n), vec![]),
			DynamicTerm::Suc(n) => Preterm::Constructor(Constructor::Suc, vec![n.unelaborate()]),
			DynamicTerm::CaseNat { scrutinee, motive_kind: _, motive, case_nil, case_suc } => {
				let case_suc = case_suc.unelaborate();
				Preterm::Split {
					scrutinee: scrutinee.unelaborate().into(),
					is_cast: false,
					motive: AnyBinder::from(motive).unelaborate(),
					cases: vec![
						(Pattern::Construction(Constructor::Num(0), vec![]), case_nil.unelaborate()),
						(
							Pattern::Construction(
								Constructor::Suc,
								vec![Pattern::Witness {
									index: case_suc.parameters[0],
									witness: case_suc.parameters[1],
								}],
							),
							*case_suc.body,
						),
					],
				}
			}

			DynamicTerm::Bx { inner, kind: _ } => Preterm::Former(Former::Bx, vec![inner.unelaborate()]),
			DynamicTerm::BxValue(v) => Preterm::Constructor(Constructor::Bx, vec![v.unelaborate()]),
			DynamicTerm::BxProject { scrutinee, kind: _ } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Bx),

			DynamicTerm::Wrap { inner, kind: _ } => Preterm::Former(Former::Wrap, vec![inner.unelaborate()]),
			DynamicTerm::WrapValue(v) => Preterm::Constructor(Constructor::Wrap, vec![v.unelaborate()]),
			DynamicTerm::WrapProject { scrutinee, kind: _ } =>
				Preterm::Project(scrutinee.unelaborate().into(), Projector::Wrap),
		})
	}
}

impl<const N: usize, T: Unelaborate> Unelaborate for Binder<Label, Box<T>, N> {
	type Pre = Binder<Label, Box<T::Pre>, N>;
	fn unelaborate(self) -> Self::Pre { Binder::new(self.parameters, self.body.unelaborate().into()) }
}

impl<T: Unelaborate> Unelaborate for AnyBinder<Label, Box<T>> {
	type Pre = AnyBinder<Label, Box<T::Pre>>;
	fn unelaborate(self) -> Self::Pre { AnyBinder::new(self.parameters, self.body.unelaborate().into()) }
}
