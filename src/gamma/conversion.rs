use super::{
	common::{Level, Projection},
	evaluator::{Autolyze, DynamicNeutral, DynamicValue, StaticNeutral, StaticValue},
};
use crate::utility::rc;

pub trait Conversion<T> {
	/// Decides whether two values are judgementally equal.
	fn can_convert(self, left: &T, right: &T) -> bool;
}

impl Conversion<StaticValue> for Level {
	fn can_convert(self, left: &StaticValue, right: &StaticValue) -> bool {
		use StaticValue::*;
		match (left, right) {
			(Universe, Universe)
			| (Nat, Nat)
			| (Bool, Bool)
			| (CopyabilityType, CopyabilityType)
			| (ReprType, ReprType)
			| (ReprNone, ReprNone) => true,
			(ReprAtom(left), ReprAtom(right)) => left == right,
			(ReprPair(left0, left1), ReprPair(right0, right1)) =>
				self.can_convert(&**left0, right0) && self.can_convert(&**left1, right1),
			(ReprMax(left0, left1), ReprMax(right0, right1)) =>
				self.can_convert(&**left0, right0) && self.can_convert(&**left1, right1),
			(Lift(left), Lift(right)) | (Quote(left), Quote(right)) => self.can_convert(left, right),
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),
			(Function(left), Function(right)) =>
				(self + 1).can_convert(&left.autolyze(self), &right.autolyze(self)),
			(Neutral(left), Function(right)) => (self + 1).can_convert(
				&Neutral(StaticNeutral::Apply(rc!(left.clone()), rc!((right.parameter(), self).into()))),
				&right.autolyze(self),
			),
			(Function(left), Neutral(right)) => (self + 1).can_convert(
				&left.autolyze(self),
				&Neutral(StaticNeutral::Apply(rc!(right.clone()), rc!((left.parameter(), self).into()))),
			),
			(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, &right_bp) && self.can_convert(&**left_fp, &right_fp),
			(IndexedProduct(left_base, left_family), IndexedProduct(right_base, right_family))
			| (IndexedSum(left_base, left_family), IndexedSum(right_base, right_family)) =>
				self.can_convert(&**left_base, right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			(Num(left), Num(right)) => left == right,
			(BoolValue(left), BoolValue(right)) => left == right,
			(Copyability(left), Copyability(right)) => left == right,
			_ => false,
		}
	}
}

impl Conversion<StaticNeutral> for Level {
	fn can_convert(self, left: &StaticNeutral, right: &StaticNeutral) -> bool {
		use StaticNeutral::*;
		match (left, right) {
			(Variable(_, left), Variable(_, right)) => left == right,
			(MaxCopyability(a_left, b_left), MaxCopyability(a_right, b_right)) =>
				self.can_convert(&**a_left, a_right) && self.can_convert(&**b_left, b_right),
			(ReprUniv(left), ReprUniv(right)) => self.can_convert(&**left, right),
			(Apply(left, left_argument), Apply(right, right_argument)) =>
				self.can_convert(&**left, &right) && self.can_convert(&**left_argument, &right_argument),
			(Project(left, left_projection), Project(right, right_projection)) =>
				left_projection == right_projection && self.can_convert(&**left, right),
			(
				CaseNat { scrutinee: l_scrutinee, motive: l_motive, case_nil: l_case_nil, case_suc: l_case_suc },
				CaseNat { scrutinee: r_scrutinee, motive: r_motive, case_nil: r_case_nil, case_suc: r_case_suc },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.autolyze(self), &r_motive.autolyze(self))
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.autolyze(self), &r_case_suc.autolyze(self)),
			(
				CaseBool { scrutinee: l_scrutinee, motive: l_motive, case_false: l_case_f, case_true: l_case_t },
				CaseBool { scrutinee: r_scrutinee, motive: r_motive, case_false: r_case_f, case_true: r_case_t },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.autolyze(self), &r_motive.autolyze(self))
					&& self.can_convert(&**l_case_f, r_case_f)
					&& self.can_convert(&**l_case_t, r_case_t),
			_ => false,
		}
	}
}

impl Conversion<DynamicValue> for Level {
	fn can_convert(self, left: &DynamicValue, right: &DynamicValue) -> bool {
		use DynamicNeutral::*;
		use DynamicValue::*;
		use Projection::*;
		match (left, right) {
			(
				Universe { copyability: left_copyability, representation: left_representation },
				Universe { copyability: right_copyability, representation: right_representation },
			) =>
				self.can_convert(&**left_copyability, right_copyability)
					&& self.can_convert(&**left_representation, right_representation),
			(WrapType(left), WrapType(right)) => self.can_convert(&**left, right),
			(WrapNew(left), WrapNew(right)) => self.can_convert(&**left, right),
			(RcType(left), RcType(right)) => self.can_convert(&**left, right),
			(RcNew(left), RcNew(right)) => self.can_convert(&**left, right),
			(Neutral(left), Neutral(right)) => self.can_convert(left, right),
			(Function { body: left, .. }, Function { body: right, .. }) =>
				(self + 1).can_convert(&left.autolyze(self), &right.autolyze(self)),
			(Neutral(left), Function { body: right, .. }) => (self + 1).can_convert(
				&Neutral(Apply(rc!(left.clone()), rc!((right.parameter(), self).into()))),
				&right.autolyze(self),
			),
			(Function { body: left, .. }, Neutral(right)) => (self + 1).can_convert(
				&left.autolyze(self),
				&Neutral(Apply(rc!(right.clone()), rc!((left.parameter(), self).into()))),
			),
			(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
				self.can_convert(&**left_bp, &right_bp) && self.can_convert(&**left_fp, &right_fp),
			(Neutral(left), Pair(right_bp, right_fp)) =>
				self.can_convert(&Neutral(Project(rc!(left.clone()), Base)), &right_bp)
					&& self.can_convert(&Neutral(Project(rc!(left.clone()), Fiber)), &right_fp),
			(Pair(left_bp, left_fp), Neutral(right)) =>
				self.can_convert(&**left_bp, &Neutral(Project(rc!(right.clone()), Base)))
					&& self.can_convert(&**left_fp, &Neutral(Project(rc!(right.clone()), Fiber))),
			(IndexedProduct(left_base, left_family), IndexedProduct(right_base, right_family))
			| (IndexedSum(left_base, left_family), IndexedSum(right_base, right_family)) =>
				self.can_convert(&**left_base, &right_base)
					&& (self + 1).can_convert(&left_family.autolyze(self), &right_family.autolyze(self)),
			(Nat, Nat) | (Bool, Bool) => true,
			(Num(left), Num(right)) => left == right,
			(BoolValue(left), BoolValue(right)) => left == right,
			_ => false,
		}
	}
}

impl Conversion<DynamicNeutral> for Level {
	fn can_convert(self, left: &DynamicNeutral, right: &DynamicNeutral) -> bool {
		use DynamicNeutral::*;
		match (left, right) {
			(Variable(_, left), Variable(_, right)) => left == right,
			(Apply(left, left_argument), Apply(right, right_argument)) =>
				self.can_convert(&**left, right) && self.can_convert(&**left_argument, right_argument),
			(Project(left, left_projection), Project(right, right_projection)) =>
				left_projection == right_projection && self.can_convert(&**left, right),
			(Unwrap(left), Unwrap(right)) | (UnRc(left), UnRc(right)) | (Suc(left), Suc(right)) =>
				self.can_convert(&**left, right),
			(Splice(left), Splice(right)) => self.can_convert(left, right),
			(
				CaseNat { scrutinee: l_scrutinee, motive: l_motive, case_nil: l_case_nil, case_suc: l_case_suc },
				CaseNat { scrutinee: r_scrutinee, motive: r_motive, case_nil: r_case_nil, case_suc: r_case_suc },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.autolyze(self), &r_motive.autolyze(self))
					&& self.can_convert(&**l_case_nil, r_case_nil)
					&& (self + 2).can_convert(&l_case_suc.autolyze(self), &r_case_suc.autolyze(self)),
			(
				CaseBool { scrutinee: l_scrutinee, motive: l_motive, case_false: l_case_f, case_true: l_case_t },
				CaseBool { scrutinee: r_scrutinee, motive: r_motive, case_false: r_case_f, case_true: r_case_t },
			) =>
				self.can_convert(&**l_scrutinee, r_scrutinee)
					&& (self + 1).can_convert(&l_motive.autolyze(self), &r_motive.autolyze(self))
					&& self.can_convert(&**l_case_f, r_case_f)
					&& self.can_convert(&**l_case_t, r_case_t),
			_ => false,
		}
	}
}
