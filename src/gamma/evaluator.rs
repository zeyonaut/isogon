use std::rc::Rc;

use super::{
	common::{bind, Binder, Closure, Copyability, Index, Level, Name, Projection, Repr, ReprAtom},
	elaborator::{DynamicTerm, StaticTerm},
};
use crate::utility::{bx, rc};

#[derive(Clone, Debug)]
pub enum StaticNeutral {
	Variable(Name, Level),
	Apply(Rc<Self>, Rc<StaticValue>),
	Project(Rc<Self>, Projection),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		case_nil: Rc<StaticValue>,
		case_suc: Rc<Closure<Environment, StaticTerm, 2>>,
	},
	Suc(Rc<Self>),
	CaseBool {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, StaticTerm>>,
		case_false: Rc<StaticValue>,
		case_true: Rc<StaticValue>,
	},
	MaxCopyability(Rc<Self>, Rc<Self>),
	ReprUniv(Rc<Self>),
}

#[derive(Clone, Debug)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	CopyabilityType,
	Copyability(Copyability),
	ReprType,
	ReprNone,
	ReprAtom(ReprAtom),
	// NOTE: This is a little type-unsafe in exchange for less redundant code; we need to make sure that these two never contain a ReprNone.
	ReprPair(Rc<Self>, Rc<Self>),
	ReprMax(Rc<Self>, Rc<Self>),
	Lift(DynamicValue),
	Quote(DynamicValue),
	IndexedProduct(Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Function(Rc<Closure<Environment, StaticTerm>>),
	IndexedSum(Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
	Bool,
	BoolValue(bool),
}

impl From<&Repr> for StaticValue {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(*atom),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Max(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
		}
	}
}

impl From<Option<&Repr>> for StaticValue {
	fn from(value: Option<&Repr>) -> Self {
		match value {
			Some(repr) => repr.into(),
			None => Self::ReprNone,
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicNeutral {
	Variable(Name, Level),
	Splice(StaticNeutral),
	Apply(Rc<Self>, Rc<DynamicValue>),
	Project(Rc<Self>, Projection),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
		case_nil: Rc<DynamicValue>,
		case_suc: Rc<Closure<Environment, DynamicTerm, 2>>,
	},
	Suc(Rc<Self>),
	CaseBool {
		scrutinee: Rc<Self>,
		motive: Rc<Closure<Environment, DynamicTerm>>,
		case_false: Rc<DynamicValue>,
		case_true: Rc<DynamicValue>,
	},
	Unwrap(Rc<Self>),
	UnRc(Rc<Self>),
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe {
		copyability: Rc<StaticValue>,
		representation: Rc<StaticValue>,
	},
	IndexedProduct {
		base_copyability: Rc<StaticValue>,
		base_representation: Rc<StaticValue>,
		base: Rc<Self>,
		family_copyability: Rc<StaticValue>,
		family_representation: Rc<StaticValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Function {
		base: Rc<Self>,
		family: Rc<Closure<Environment, DynamicTerm>>,
		body: Rc<Closure<Environment, DynamicTerm>>,
	},
	IndexedSum {
		base_copyability: Rc<StaticValue>,
		base_representation: Rc<StaticValue>,
		base: Rc<Self>,
		family_copyability: Rc<StaticValue>,
		family_representation: Rc<StaticValue>,
		family: Rc<Closure<Environment, DynamicTerm>>,
	},
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
	Bool,
	BoolValue(bool),
	WrapType(Rc<Self>),
	WrapNew(Rc<Self>),
	RcType(Rc<Self>),
	RcNew(Rc<Self>),
}

impl StaticValue {
	pub fn max_copyability(a: Self, b: Self) -> Self {
		use Copyability as C;
		match (a, b) {
			(Self::Copyability(C::Nontrivial), _) => Self::Copyability(C::Nontrivial),
			(Self::Copyability(C::Trivial), b) => b,
			(_, Self::Copyability(C::Nontrivial)) => Self::Copyability(C::Nontrivial),
			(a, Self::Copyability(C::Trivial)) => a,
			(Self::Neutral(a), Self::Neutral(b)) => Self::Neutral(StaticNeutral::MaxCopyability(rc!(a), rc!(b))),
			_ => panic!(),
		}
	}

	pub fn pair_representation(a: Self, b: Self) -> Self {
		match (a, b) {
			(Self::ReprNone, b) => b,
			(a, Self::ReprNone) => a,
			(a, b) => Self::ReprPair(rc!(a), rc!(b)),
		}
	}

	pub fn max_representation(a: Self, b: Self) -> Self {
		match (a, b) {
			(Self::ReprNone, b) => b,
			(a, Self::ReprNone) => a,
			(a, b) => Self::ReprMax(rc!(a), rc!(b)),
		}
	}

	pub fn univ_representation(c: Self) -> Self {
		match c {
			StaticValue::Neutral(n) => StaticValue::Neutral(StaticNeutral::ReprUniv(rc!(n))),
			StaticValue::Copyability(Copyability::Trivial) => StaticValue::ReprNone,
			StaticValue::Copyability(Copyability::Nontrivial) => StaticValue::ReprAtom(ReprAtom::Class),
			_ => panic!(),
		}
	}
}

impl From<(Name, Level)> for StaticValue {
	fn from((name, level): (Name, Level)) -> Self {
		Self::Neutral(StaticNeutral::Variable(name, level))
	}
}

impl From<(Name, Level)> for DynamicValue {
	fn from((name, level): (Name, Level)) -> Self {
		Self::Neutral(DynamicNeutral::Variable(name, level))
	}
}

impl DynamicValue {
	pub fn reify_closed(&self) -> DynamicTerm {
		self.reify(Level(0))
	}
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone, Debug)]
pub struct Environment(pub Vec<Value>);

impl Environment {
	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.0.extend(values);
		environment
	}

	pub fn push(&mut self, value: Value) {
		self.0.push(value);
	}
}

pub trait Evaluate {
	type Value;
	/// Transforms a core term into a value.
	fn evaluate(self, environment: &Environment) -> Self::Value;
}

impl<T, const N: usize> Evaluate for Binder<Box<T>, N> {
	type Value = Closure<Environment, T, N>;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Evaluate for StaticTerm {
	type Value = StaticValue;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		use StaticTerm::*;
		match self {
			Variable(_, index) => environment.lookup_static(index),
			CopyabilityType => StaticValue::CopyabilityType,
			Copyability(c) => StaticValue::Copyability(c),
			MaxCopyability(a, b) => {
				let a = a.evaluate(environment);
				let b = b.evaluate(environment);
				StaticValue::max_copyability(a, b)
			}
			ReprType => StaticValue::ReprType,
			ReprAtom(r) => r.map(StaticValue::ReprAtom).unwrap_or(StaticValue::ReprNone),
			ReprPair(r0, r1) => {
				let r0 = r0.evaluate(environment);
				let r1 = r1.evaluate(environment);
				StaticValue::pair_representation(r0, r1)
			}
			ReprMax(r0, r1) => {
				let r0 = r0.evaluate(environment);
				let r1 = r1.evaluate(environment);
				StaticValue::max_representation(r0, r1)
			}
			ReprUniv(c) => {
				let c = c.evaluate(environment);
				StaticValue::univ_representation(c)
			}
			Pi(base, family) =>
				StaticValue::IndexedProduct(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Lambda(function) => StaticValue::Function(rc!(function.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				StaticValue::Function(function) => function.evaluate_with([argument.evaluate(environment)]),
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Apply(rc!(neutral), rc!(argument.evaluate(environment)))),
				_ => panic!(),
			},
			Sigma(base, family) =>
				StaticValue::IndexedSum(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Pair { basepoint, fiberpoint } =>
				StaticValue::Pair(rc!(basepoint.evaluate(environment)), rc!(fiberpoint.evaluate(environment))),
			Project(scrutinee, projection) => match scrutinee.evaluate(environment) {
				StaticValue::Pair(basepoint, fiberpoint) => match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				},
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Project(rc!(neutral), projection)),
				_ => panic!(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate(environment)]),
			Universe => StaticValue::Universe,
			Lift(liftee) => StaticValue::Lift(liftee.evaluate(environment)),
			Quote(quotee) => StaticValue::Quote(quotee.evaluate(environment)),
			Nat => StaticValue::Nat,
			Num(n) => StaticValue::Num(n),
			Suc(prev) => match prev.evaluate(environment) {
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::Suc(rc!(neutral))),
				StaticValue::Num(n) => StaticValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate(environment) {
				StaticValue::Num(n) => (0..n).fold(case_nil.evaluate(environment), |previous, i| {
					case_suc.evaluate_at(environment, [StaticValue::Num(i), previous])
				}),
				StaticValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let StaticNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(&previous);
					}
					let result = StaticValue::Neutral(StaticNeutral::CaseNat {
						scrutinee: rc!(neutrals.pop().unwrap().clone()),
						motive: rc!(motive.evaluate(environment)),
						case_nil: rc!(case_nil.evaluate(environment)),
						case_suc: rc!(case_suc.clone().evaluate(environment)),
					});
					neutrals
						.into_iter()
						.rev()
						.cloned()
						.map(StaticValue::Neutral)
						.fold(result, |previous, number| case_suc.evaluate_at(environment, [number, previous]))
				}
				_ => panic!(),
			},
			Bool => StaticValue::Bool,
			BoolValue(b) => StaticValue::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => match scrutinee.evaluate(environment) {
				StaticValue::BoolValue(b) => if b { case_true } else { case_false }.evaluate(environment),
				StaticValue::Neutral(neutral) => StaticValue::Neutral(StaticNeutral::CaseBool {
					scrutinee: rc!(neutral),
					motive: rc!(motive.evaluate(environment)),
					case_false: rc!(case_false.evaluate(environment)),
					case_true: rc!(case_true.evaluate(environment)),
				}),
				_ => panic!(),
			},
		}
	}
}

impl Evaluate for DynamicTerm {
	type Value = DynamicValue;
	fn evaluate(self, environment: &Environment) -> Self::Value {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => DynamicValue::Function {
				base: base.evaluate(environment).into(),
				family: family.evaluate(environment).into(),
				body: body.evaluate(environment).into(),
			},
			Pair { basepoint, fiberpoint } =>
				DynamicValue::Pair(rc!(basepoint.evaluate(environment)), rc!(fiberpoint.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				DynamicValue::Function { body, .. } => body.evaluate_with([argument.evaluate(environment)]),
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Apply(rc!(neutral), rc!(argument.evaluate(environment)))),
				_ => panic!(),
			},
			Project(scrutinee, projection) => match scrutinee.evaluate(environment) {
				DynamicValue::Pair(basepoint, fiberpoint) => match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				},
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Project(rc!(neutral), projection)),
				_ => panic!(),
			},
			Pi {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedProduct {
				base_copyability: base_copyability.into(),
				base_representation: base_representation.into(),
				base: base.evaluate(environment).into(),
				family_copyability: family_copyability.into(),
				family_representation: family_representation.into(),
				family: family.evaluate(environment).into(),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => DynamicValue::IndexedSum {
				base_copyability: base_copyability.into(),
				base_representation: base_representation.into(),
				base: base.evaluate(environment).into(),
				family_copyability: family_copyability.into(),
				family_representation: family_representation.into(),
				family: family.evaluate(environment).into(),
			},
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate(environment)]),
			Universe { copyability, representation } => DynamicValue::Universe {
				copyability: rc!(copyability.evaluate(environment)),
				representation: rc!(representation.evaluate(environment)),
			},
			Splice(splicee) => match splicee.evaluate(environment) {
				StaticValue::Quote(quotee) => quotee,
				StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
				_ => panic!(),
			},
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => match prev.evaluate(environment) {
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Suc(rc!(neutral))),
				DynamicValue::Num(n) => DynamicValue::Num(n + 1),
				_ => panic!(),
			},
			CaseNat { scrutinee, motive, case_nil, case_suc } => match scrutinee.evaluate(environment) {
				DynamicValue::Num(n) => (0..n).fold(case_nil.evaluate(environment), |previous, i| {
					case_suc.evaluate_at(environment, [DynamicValue::Num(i), previous])
				}),
				DynamicValue::Neutral(neutral) => {
					let mut neutrals = vec![&neutral];
					while let DynamicNeutral::Suc(previous) = neutrals.last().unwrap() {
						neutrals.push(&previous);
					}
					let result = DynamicValue::Neutral(DynamicNeutral::CaseNat {
						scrutinee: rc!(neutrals.pop().unwrap().clone()),
						motive: rc!(motive.evaluate(environment)),
						case_nil: rc!(case_nil.evaluate(environment)),
						case_suc: rc!(case_suc.clone().evaluate(environment)),
					});
					neutrals
						.into_iter()
						.rev()
						.cloned()
						.map(DynamicValue::Neutral)
						.fold(result, |previous, number| case_suc.evaluate_at(environment, [number, previous]))
				}
				_ => panic!(),
			},
			Bool => DynamicValue::Bool,
			BoolValue(b) => DynamicValue::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => match scrutinee.evaluate(environment) {
				DynamicValue::BoolValue(b) => if b { case_true } else { case_false }.evaluate(environment),
				DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::CaseBool {
					scrutinee: rc!(neutral),
					motive: rc!(motive.evaluate(environment)),
					case_false: rc!(case_false.evaluate(environment)),
					case_true: rc!(case_true.evaluate(environment)),
				}),
				_ => panic!(),
			},
			WrapType(ty) => DynamicValue::WrapType(rc!(ty.evaluate(environment))),
			WrapNew(tm) => DynamicValue::WrapNew(rc!(tm.evaluate(environment))),
			Unwrap(tm) => match tm.evaluate(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::Unwrap(rc!(n))),
				DynamicValue::WrapNew(v) => v.as_ref().clone(),
				_ => panic!(),
			},
			RcType(ty) => DynamicValue::RcType(rc!(ty.evaluate(environment))),
			RcNew(tm) => DynamicValue::RcNew(rc!(tm.evaluate(environment))),
			UnRc(tm) => match tm.evaluate(environment) {
				DynamicValue::Neutral(n) => DynamicValue::Neutral(DynamicNeutral::UnRc(rc!(n))),
				DynamicValue::RcNew(v) => v.as_ref().clone(),
				_ => panic!(),
			},
		}
	}
}

pub trait EvaluateWith<const N: usize> {
	type Value;
	/// Transforms a core closure under a binder into a value, taking arguments.
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value;
}

impl<const N: usize> EvaluateWith<N> for &Closure<Environment, StaticTerm, N> {
	type Value = StaticValue;
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&self.environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateWith<N> for &Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn evaluate_with(self, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&self.environment.extend(arguments.map(Value::Dynamic)))
	}
}

pub trait EvaluateAt<const N: usize> {
	type Value;
	/// Transforms a core term under a binder into a value, taking arguments.
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value;
}

impl<const N: usize> EvaluateAt<N> for &Binder<Box<StaticTerm>, N> {
	type Value = StaticValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&environment.extend(arguments.map(Value::Static)))
	}
}

impl<const N: usize> EvaluateAt<N> for &Binder<Box<DynamicTerm>, N> {
	type Value = DynamicValue;
	fn evaluate_at(self, environment: &Environment, arguments: [Self::Value; N]) -> Self::Value {
		self.body.clone().evaluate(&environment.extend(arguments.map(Value::Dynamic)))
	}
}

pub trait Autolyze {
	type Value;
	/// Evaluates a closure on its own parameters by postulating them and passing them in.
	fn autolyze(&self, context_len: Level) -> Self::Value;
}

impl<const N: usize> Autolyze for Closure<Environment, StaticTerm, N> {
	type Value = StaticValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}

impl<const N: usize> Autolyze for Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn autolyze(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.evaluate_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			(parameter, y).into()
		}))
	}
}

pub trait Reify {
	type Term;
	/// Transforms a value into a core term.
	fn reify(&self, level: Level) -> Self::Term;
}

impl<const N: usize> Reify for Closure<Environment, StaticTerm, N> {
	type Term = Binder<Box<StaticTerm>, N>;
	fn reify(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify(level + N)))
	}
}

impl<const N: usize> Reify for Closure<Environment, DynamicTerm, N> {
	type Term = Binder<Box<DynamicTerm>, N>;
	fn reify(&self, level: Level) -> Self::Term {
		bind(self.parameters, bx!(self.autolyze(level).reify(level + N)))
	}
}

impl Reify for StaticNeutral {
	type Term = StaticTerm;
	fn reify(&self, level @ Level(context_length): Level) -> Self::Term {
		use StaticNeutral::*;
		match self {
			Variable(name, Level(level)) => StaticTerm::Variable(*name, Index(context_length - 1 - level)),
			MaxCopyability(a, b) => StaticTerm::MaxCopyability(bx!(a.reify(level)), bx!(b.reify(level))),
			ReprUniv(c) => StaticTerm::ReprUniv(bx!(c.reify(level))),
			Apply(callee, argument) =>
				StaticTerm::Apply { scrutinee: bx!(callee.reify(level)), argument: bx!(argument.reify(level)) },
			Project(scrutinee, projection) => StaticTerm::Project(bx!(scrutinee.reify(level)), *projection),
			Suc(prev) => StaticTerm::Suc(bx!(prev.reify(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => StaticTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_nil: bx!(case_nil.reify(level)),
				case_suc: case_suc.reify(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => StaticTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_false: bx!(case_false.reify(level)),
				case_true: bx!(case_true.reify(level)),
			},
		}
	}
}

impl Reify for StaticValue {
	type Term = StaticTerm;
	fn reify(&self, level: Level) -> Self::Term {
		use StaticValue::*;
		match self {
			Neutral(neutral) => neutral.reify(level),
			Universe => StaticTerm::Universe,
			IndexedProduct(base, family) => StaticTerm::Pi(bx!(base.reify(level)), family.reify(level)),
			Function(function) => StaticTerm::Lambda(function.reify(level)),
			IndexedSum(base, family) => StaticTerm::Sigma(bx!(base.reify(level)), family.reify(level)),
			Pair(basepoint, fiberpoint) => StaticTerm::Pair {
				basepoint: bx!(basepoint.reify(level)),
				fiberpoint: bx!(fiberpoint.reify(level)),
			},
			Lift(liftee) => StaticTerm::Lift(bx!(liftee.reify(level))),
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.reify(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Bool => StaticTerm::Bool,
			BoolValue(b) => StaticTerm::BoolValue(*b),
			CopyabilityType => StaticTerm::CopyabilityType,
			Copyability(c) => StaticTerm::Copyability(*c),
			ReprType => StaticTerm::ReprType,
			ReprNone => StaticTerm::ReprAtom(None),
			ReprAtom(r) => StaticTerm::ReprAtom(Some(*r)),
			ReprPair(r0, r1) => StaticTerm::ReprPair(bx!(r0.reify(level)), bx!(r1.reify(level))),
			ReprMax(r0, r1) => StaticTerm::ReprMax(bx!(r0.reify(level)), bx!(r1.reify(level))),
		}
	}
}

impl Reify for DynamicNeutral {
	type Term = DynamicTerm;
	fn reify(&self, level @ Level(context_length): Level) -> Self::Term {
		use DynamicNeutral::*;
		match self {
			Variable(name, Level(level)) => DynamicTerm::Variable(*name, Index(context_length - 1 - level)),
			Splice(splicee) => DynamicTerm::Splice(bx!(splicee.reify(level))),
			Apply(callee, argument) =>
				DynamicTerm::Apply { scrutinee: bx!(callee.reify(level)), argument: bx!(argument.reify(level)) },
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.reify(level)), *projection),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.reify(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_nil: bx!(case_nil.reify(level)),
				case_suc: case_suc.reify(level),
			},
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.reify(level)),
				motive: motive.reify(level),
				case_false: bx!(case_false.reify(level)),
				case_true: bx!(case_true.reify(level)),
			},
			Unwrap(v) => DynamicTerm::Unwrap(bx!(v.reify(level))),
			UnRc(v) => DynamicTerm::UnRc(bx!(v.reify(level))),
		}
	}
}

impl Reify for DynamicValue {
	type Term = DynamicTerm;
	fn reify(&self, level: Level) -> Self::Term {
		use DynamicValue::*;
		match self {
			Neutral(neutral) => neutral.reify(level),
			Universe { copyability, representation } => DynamicTerm::Universe {
				copyability: bx!(copyability.reify(level)),
				representation: bx!(representation.reify(level)),
			},
			IndexedProduct {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Pi {
				base_copyability: (**base_copyability).clone(),
				base_representation: (**base_representation).clone(),
				base: base.reify(level).into(),
				family_copyability: (**base_copyability).clone(),
				family_representation: (**base_representation).clone(),
				family: family.reify(level),
			},
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.reify(level).into(),
				family: family.reify(level).into(),
				body: body.reify(level).into(),
			},
			IndexedSum {
				base_copyability,
				base_representation,
				base,
				family_copyability: _,
				family_representation: _,
				family,
			} => DynamicTerm::Sigma {
				base_copyability: (**base_copyability).clone(),
				base_representation: (**base_representation).clone(),
				base: base.reify(level).into(),
				family_copyability: (**base_copyability).clone(),
				family_representation: (**base_representation).clone(),
				family: family.reify(level),
			},
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: bx!(basepoint.reify(level)),
				fiberpoint: bx!(fiberpoint.reify(level)),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			WrapType(x) => DynamicTerm::WrapType(bx!(x.reify(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.reify(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.reify(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.reify(level))),
		}
	}
}
