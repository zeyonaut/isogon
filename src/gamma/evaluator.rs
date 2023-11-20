use std::rc::Rc;

use super::{
	common::{bind, Binder, Closure, Index, Level, Name, Projection},
	elaborator::{DynamicTerm, StaticTerm},
};
use crate::utility::{bx, rc};

#[derive(Clone)]
pub enum StaticNeutral {
	Variable(Name, Level),
	Apply(Rc<Self>, Rc<StaticValue>),
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
}

#[derive(Clone)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	Lift(DynamicValue),
	Quote(DynamicValue),
	IndexedProduct(Rc<Self>, Rc<Closure<Environment, StaticTerm>>),
	Function(Rc<Closure<Environment, StaticTerm>>),
	Nat,
	Num(usize),
	Bool,
	BoolValue(bool),
}

#[derive(Clone)]
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
}

#[derive(Clone)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe,
	IndexedProduct(Rc<Self>, Rc<Closure<Environment, DynamicTerm>>),
	Function(Rc<Closure<Environment, DynamicTerm>>),
	IndexedSum(Rc<Self>, Rc<Closure<Environment, DynamicTerm>>),
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
	Bool,
	BoolValue(bool),
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

#[derive(Clone)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone)]
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
			Lambda(function) => StaticValue::Function(rc!(function.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				StaticValue::Function(function) => function.evaluate_with([argument.evaluate(environment)]),
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Apply(rc!(neutral), rc!(argument.evaluate(environment)))),
				_ => panic!(),
			},
			Pi(base, family) =>
				StaticValue::IndexedProduct(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
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
			Lambda(function) => DynamicValue::Function(rc!(function.evaluate(environment))),
			Pair { basepoint, fiberpoint } =>
				DynamicValue::Pair(rc!(basepoint.evaluate(environment)), rc!(fiberpoint.evaluate(environment))),
			Apply { scrutinee, argument } => match scrutinee.evaluate(environment) {
				DynamicValue::Function(function) => function.evaluate_with([argument.evaluate(environment)]),
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
			Pi(base, family) =>
				DynamicValue::IndexedProduct(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Sigma(base, family) =>
				DynamicValue::IndexedSum(rc!(base.evaluate(environment)), rc!(family.evaluate(environment))),
			Let { argument, tail, .. } => tail.evaluate_at(environment, [argument.evaluate(environment)]),
			Universe => DynamicValue::Universe,
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
			Apply(callee, argument) =>
				StaticTerm::Apply { scrutinee: bx!(callee.reify(level)), argument: bx!(argument.reify(level)) },
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
			Lift(liftee) => StaticTerm::Lift(bx!(liftee.reify(level))),
			Quote(quotee) => StaticTerm::Quote(bx!(quotee.reify(level))),
			Nat => StaticTerm::Nat,
			Num(n) => StaticTerm::Num(*n),
			Bool => StaticTerm::Bool,
			BoolValue(b) => StaticTerm::BoolValue(*b),
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
		}
	}
}

impl Reify for DynamicValue {
	type Term = DynamicTerm;
	fn reify(&self, level: Level) -> Self::Term {
		use DynamicValue::*;
		match self {
			Neutral(neutral) => neutral.reify(level),
			Universe => DynamicTerm::Universe,
			IndexedProduct(base, family) => DynamicTerm::Pi(bx!(base.reify(level)), family.reify(level)),
			Function(function) => DynamicTerm::Lambda(function.reify(level)),
			IndexedSum(base, family) => DynamicTerm::Sigma(bx!(base.reify(level)), family.reify(level)),
			Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
				basepoint: bx!(basepoint.reify(level)),
				fiberpoint: bx!(fiberpoint.reify(level)),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
		}
	}
}
