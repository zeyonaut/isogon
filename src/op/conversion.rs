use std::rc::Rc;

use crate::delta::{
	common::{Field, Level},
	ir::semantics::{CpyValue, DynamicNeutral, DynamicValue, KindValue, StaticNeutral, StaticValue},
	op::evaluate::EvaluateAuto,
};

pub trait Conversion<T> {
	/// Decides whether two values are judgementally equal.
	fn can_convert(self, left: &T, right: &T) -> bool;
}

impl Conversion<KindValue> for Level {
	fn can_convert(self, left: &KindValue, right: &KindValue) -> bool {
		self.can_convert(&left.copy, &right.copy) && self.can_convert(&left.repr, &right.repr)
	}
}

impl Conversion<StaticValue> for Level {
	fn can_convert(self, left: &StaticValue, right: &StaticValue) -> bool {
		use StaticValue as V;
		match (left, right) {
			// Neutrals.
			(V::Neutral(left), V::Neutral(right)) => self.can_convert(left, right),

			// Types and universe indidces.
			(V::Universe(l), V::Universe(r)) => l == r,

			(V::Cpy, V::Cpy) => true,
			(V::CpyValue(CpyValue::Nt), V::CpyValue(CpyValue::Nt)) => true,
			(V::CpyValue(CpyValue::Max(a_set)), V::CpyValue(CpyValue::Max(b_set)))
				if a_set.len() == b_set.len() =>
			{
				let mut a_compared = vec![false; a_set.len()];
				'b: for b in b_set {
					'a: for (i, a) in a_set.iter().enumerate() {
						if a_compared[i] {
							continue 'a;
						}

						if self.can_convert(a, b) {
							a_compared[i] = true;
							continue 'b;
						}
					}
					return false;
				}
				true
			}
			(V::CpyValue(CpyValue::Max(left)), V::Neutral(right)) if left.len() == 1 =>
				self.can_convert(&left[0], right),
			(V::Neutral(left), V::CpyValue(CpyValue::Max(right))) if right.len() == 1 =>
				self.can_convert(left, &right[0]),

			(V::ReprType, V::ReprType) | (V::ReprNone, V::ReprNone) => true,
			(V::ReprAtom(left), V::ReprAtom(right)) => left == right,
			(V::ReprExp(a, l), V::ReprExp(b, r)) => a == b && self.can_convert(&**l, r),
			(V::ReprPair(a, b), V::ReprPair(s, t)) => self.can_convert(&**a, s) && self.can_convert(&**b, t),

			// Quoted programs.
			(V::Lift { ty: left, .. }, V::Lift { ty: right, .. }) | (V::Quote(left), V::Quote(right)) =>
				self.can_convert(left, right),

			// Repeated programs.
			(V::Exp(grade_l, _, ty_l), V::Exp(grade_r, _, ty_r)) =>
				grade_l == grade_r && self.can_convert(&**ty_l, ty_r),
			(V::Repeat(_, left), V::Repeat(_, right)) => self.can_convert(&**left, right),

			// Dependent functions.
			(
				V::IndexedProduct { grade: left_grade, base: left_base, family: left_family, .. },
				V::IndexedProduct { grade: right_grade, base: right_base, family: right_family, .. },
			) =>
				left_grade == right_grade
					&& self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.evaluate_auto(self), &right_family.evaluate_auto(self)),
			(V::Function(_, left), V::Function(_, right)) =>
				(self + 1).can_convert(&left.evaluate_auto(self), &right.evaluate_auto(self)),
			(V::Neutral(left), V::Function(_, right)) => (self + 1).can_convert(
				&V::Neutral(StaticNeutral::Apply(left.clone().into(), Rc::new((right.parameter(), self).into()))),
				&right.evaluate_auto(self),
			),
			(V::Function(_, left), V::Neutral(right)) => (self + 1).can_convert(
				&left.evaluate_auto(self),
				&V::Neutral(StaticNeutral::Apply(right.clone().into(), Rc::new((left.parameter(), self).into()))),
			),

			// Dependent pairs.
			(
				V::IndexedSum { base: left_base, family: left_family, .. },
				V::IndexedSum { base: right_base, family: right_family, .. },
			) =>
				self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.evaluate_auto(self), &right_family.evaluate_auto(self)),
			(V::Pair(left_bp, left_fp), V::Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, right_bp) && self.can_convert(&**left_fp, right_fp),
			(V::Neutral(left), V::Pair(br, fr)) =>
				self.can_convert(&V::Neutral(StaticNeutral::Project(left.clone().into(), Field::Base)), br)
					&& self.can_convert(&V::Neutral(StaticNeutral::Project(left.clone().into(), Field::Fiber)), fr),
			(V::Pair(bl, fl), V::Neutral(right)) =>
				self.can_convert(&**bl, &V::Neutral(StaticNeutral::Project(right.clone().into(), Field::Base)))
					&& self
						.can_convert(&**fl, &V::Neutral(StaticNeutral::Project(right.clone().into(), Field::Fiber))),

			// Enumerated numbers.
			(V::Enum(left), V::Enum(right)) => left == right,
			(V::EnumValue(_, left), V::EnumValue(_, right)) => left == right,

			// Natural numbers.
			(V::Nat, V::Nat) => true,
			(V::Num(l), V::Num(r)) => l == r,

			// Inconvertible.
			_ => false,
		}
	}
}

impl Conversion<StaticNeutral> for Level {
	fn can_convert(self, left: &StaticNeutral, right: &StaticNeutral) -> bool {
		use StaticNeutral::*;
		match (left, right) {
			// Variables.
			(Variable(_, left), Variable(_, right)) => left == right,

			// Repeated programs.
			(ExpProject(left), ExpProject(right)) => self.can_convert(&**left, right),

			// Dependent functions.
			(Apply(left, left_argument), Apply(right, right_argument)) =>
				self.can_convert(&**left, right) && self.can_convert(&**left_argument, right_argument),

			// Dependent pairs.
			(Project(left, left_projection), Project(right, right_projection)) =>
				left_projection == right_projection && self.can_convert(&**left, right),

			// Enumerated numbers.
			(
				CaseEnum { scrutinee: l_scrutinee, cases: l_cases, .. },
				CaseEnum { scrutinee: r_scrutinee, cases: r_cases, .. },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& l_cases
						.iter()
						.zip(r_cases.iter())
						.fold(true, |acc, (left, right)| acc && self.can_convert(left, right)),

			// Natural numbers.
			(Suc(a), Suc(b)) => self.can_convert(&**a, b),
			(
				CaseNat { scrutinee: l_scrutinee, motive: l_motive, case_nil: l_case_nil, case_suc: l_case_suc },
				CaseNat { scrutinee: r_scrutinee, motive: r_motive, case_nil: r_case_nil, case_suc: r_case_suc },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.evaluate_auto(self), &r_motive.evaluate_auto(self))
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.evaluate_auto(self), &r_case_suc.evaluate_auto(self)),

			// Inconvertible.
			_ => false,
		}
	}
}

impl Conversion<DynamicValue> for Level {
	fn can_convert(self, left: &DynamicValue, right: &DynamicValue) -> bool {
		use DynamicNeutral::*;
		use DynamicValue::*;
		use Field::*;
		match (left, right) {
			// Neutrals.
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),

			// Universes.
			(Universe { kind: kl }, Universe { kind: kr }) => self.can_convert(&**kl, kr),

			// Exponentials.
			(Exp(grade_l, _, ty_l), Exp(grade_r, _, ty_r)) =>
				grade_l == grade_r && self.can_convert(&**ty_l, ty_r),
			(Repeat(_, left), Repeat(_, right)) => self.can_convert(&**left, right),

			// Dependent functions.
			// NOTE: Annotation conversion not implemented, as it's unclear if it gives any useful advantages.
			(
				IndexedProduct { base: left_base, family: left_family, .. },
				IndexedProduct { base: right_base, family: right_family, .. },
			) =>
				self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.evaluate_auto(self), &right_family.evaluate_auto(self)),
			(Function { body: left, .. }, Function { body: right, .. }) =>
				(self + 1).can_convert(&left.evaluate_auto(self), &right.evaluate_auto(self)),
			(Neutral(left), Function { body: right, .. }) => (self + 1).can_convert(
				&Neutral(Apply {
					scrutinee: left.clone().into(),
					argument: Rc::new((right.parameter(), self).into()),
				}),
				&right.evaluate_auto(self),
			),
			(Function { body: left, .. }, Neutral(right)) => (self + 1).can_convert(
				&left.evaluate_auto(self),
				&Neutral(Apply {
					scrutinee: right.clone().into(),
					argument: Rc::new((left.parameter(), self).into()),
				}),
			),

			// Dependent pairs.
			// NOTE: Annotation conversion not implemented, as it's unclear if it gives any useful advantages.
			(
				IndexedSum { base: left_base, family: left_family, .. },
				IndexedSum { base: right_base, family: right_family, .. },
			) =>
				self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.evaluate_auto(self), &right_family.evaluate_auto(self)),
			(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, right_bp) && self.can_convert(&**left_fp, right_fp),
			(Neutral(left), Pair(right_bp, right_fp)) =>
				self.can_convert(&Neutral(Project { scrutinee: left.clone().into(), projection: Base }), right_bp)
					&& self.can_convert(
						&Neutral(Project { scrutinee: left.clone().into(), projection: Fiber }),
						right_fp,
					),
			(Pair(left_bp, left_fp), Neutral(right)) =>
				self.can_convert(
					&**left_bp,
					&Neutral(Project { scrutinee: right.clone().into(), projection: Base }),
				) && self.can_convert(
					&**left_fp,
					&Neutral(Project { scrutinee: right.clone().into(), projection: Fiber }),
				),

			// Enumerated numbers.
			(Enum(left), Enum(right)) => left == right,
			(EnumValue(_, left), EnumValue(_, right)) => left == right,

			// Paths.
			(Id { left: left_l, right: right_l, .. }, Id { left: left_r, right: right_r, .. }) =>
				self.can_convert(&**left_l, left_r) && self.can_convert(&**right_l, right_r),
			(Refl, Refl) => true,

			// Natural numbers.
			(Nat, Nat) => true,
			(Num(l), Num(r)) => l == r,

			// Wrappers.
			(Bx { inner: left, .. }, Bx { inner: right, .. })
			| (BxValue(left), BxValue(right))
			| (Wrap { inner: left, .. }, Wrap { inner: right, .. })
			| (WrapValue(left), WrapValue(right)) => self.can_convert(&**left, right),

			// Inconvertible.
			_ => false,
		}
	}
}

impl Conversion<DynamicNeutral> for Level {
	fn can_convert(self, left: &DynamicNeutral, right: &DynamicNeutral) -> bool {
		use DynamicNeutral::*;
		match (left, right) {
			// Variables.
			(Variable(_, left), Variable(_, right)) => left == right,

			// Quoted programs.
			(Splice(left), Splice(right)) => self.can_convert(left, right),

			// Repeated programs.
			(ExpProject(left), ExpProject(right)) => self.can_convert(&**left, right),

			// Dependent functions.
			(
				Apply { scrutinee: left, argument: left_argument, .. },
				Apply { scrutinee: right, argument: right_argument, .. },
			) => self.can_convert(&**left, right) && self.can_convert(&**left_argument, right_argument),

			// Enumerated numbers.
			(
				CaseEnum { scrutinee: l_scrutinee, cases: l_cases, .. },
				CaseEnum { scrutinee: r_scrutinee, cases: r_cases, .. },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& l_cases
						.iter()
						.zip(r_cases.iter())
						.fold(true, |acc, (left, right)| acc && self.can_convert(left, right)),

			// Paths.
			(
				CasePath { scrutinee: scrutinee_l, case_refl: case_l, .. },
				CasePath { scrutinee: scrutinee_r, case_refl: case_r, .. },
			) => self.can_convert(&**scrutinee_l, scrutinee_r) && self.can_convert(&**case_l, case_r),

			// Natural numbers.
			(Suc(a), Suc(b)) => self.can_convert(&**a, b),
			(
				CaseNat { scrutinee: l_scrutinee, motive: l_motive, case_nil: l_case_nil, case_suc: l_case_suc },
				CaseNat { scrutinee: r_scrutinee, motive: r_motive, case_nil: r_case_nil, case_suc: r_case_suc },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.evaluate_auto(self), &r_motive.evaluate_auto(self))
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.evaluate_auto(self), &r_case_suc.evaluate_auto(self)),

			// Wrappers.
			(BxProject(left), BxProject(right)) | (WrapProject(left), WrapProject(right)) =>
				self.can_convert(&**left, right),

			// Inconvertible.
			_ => false,
		}
	}
}
