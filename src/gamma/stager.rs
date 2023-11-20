use std::{fmt::Debug, rc::Rc};

use super::{
	common::{Binder, Closure, Index, Level, Name, Projection},
	elaborator::{DynamicTerm, StaticTerm},
};
use crate::utility::{bx, rc};

#[derive(Clone)]
pub enum StaticValue {
	Type,
	Quote(Rc<DynamicValue>),
	Function(Closure<Environment, StaticTerm>),
	Pair(Rc<Self>, Rc<Self>),
	Num(usize),
	BoolValue(bool),
}

impl Debug for StaticValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Type => write!(f, "Type"),
			Self::Quote(quotee) => f.debug_tuple("Quote").field(quotee).finish(),
			Self::Function(_) => f.debug_tuple("Function").field(&format_args!("_")).finish(),
			_ => write!(f, "<...>"),
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Variable(Name, Level),
	Let {
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Binder<Rc<Self>>,
	},
	Universe,
	Pi(Rc<Self>, Binder<Rc<Self>>),
	Function(Binder<Rc<Self>>),
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<Self>,
	},
	Sigma(Rc<Self>, Binder<Rc<Self>>),
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	Project(Rc<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_nil: Rc<Self>,
		case_suc: Binder<Rc<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_false: Rc<Self>,
		case_true: Rc<Self>,
	},
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(StaticValue),
	Dynamic(Name, Level),
}

#[derive(Clone)]
pub struct Environment {
	values: Vec<Value>,
	dynamic_context_length: Level,
}

impl Environment {
	pub fn new() -> Self {
		Self { values: Vec::new(), dynamic_context_length: Level(0) }
	}

	pub fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(name, level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		DynamicValue::Variable(*name, *level)
	}

	#[must_use]
	pub fn bind<const N: usize>(&self, names: [Name; N]) -> Self {
		let mut environment = self.clone();
		for name in names {
			environment.values.push(Value::Dynamic(name, environment.dynamic_context_length));
			environment.dynamic_context_length += 1;
		}
		environment
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.values.extend(values);
		environment
	}
}

pub trait Stage {
	type ObjectTerm;
	/// Transforms a core term into an object term.
	fn stage(self, environment: &Environment) -> Self::ObjectTerm;
}

impl<const N: usize> Stage for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Closure<Environment, StaticTerm, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Stage for StaticTerm {
	type ObjectTerm = StaticValue;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		use StaticTerm::*;
		match self {
			Variable(_, index) => environment.lookup_static(index),
			Lambda(function) => StaticValue::Function(function.stage(environment)),
			Apply { scrutinee, argument } => {
				let StaticValue::Function(function) = scrutinee.stage(environment) else { panic!() };
				// TODO: The environment argument is useless in this position: make a separate trait for this (as in EvaluateWith/EvaluateAt).
				function.stage_with(environment, [argument.stage(environment)])
			}
			Pi(..) => StaticValue::Type,
			Sigma(..) => StaticValue::Type,
			Pair { basepoint, fiberpoint } =>
				StaticValue::Pair(rc!(basepoint.stage(environment)), rc!(fiberpoint.stage(environment))),
			Project(scrutinee, projection) => {
				let StaticValue::Pair(basepoint, fiberpoint) = scrutinee.stage(environment) else { panic!() };
				match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			Let { argument, tail, .. } => tail.stage_with(environment, [argument.stage(environment)]),
			Universe => StaticValue::Type,
			Lift(_) => StaticValue::Type,
			Quote(term) => StaticValue::Quote(rc!(term.stage(environment))),
			Nat => StaticValue::Type,
			Num(n) => StaticValue::Num(n),
			Suc(p) => {
				let StaticValue::Num(p) = p.stage(environment) else { panic!() };
				StaticValue::Num(p + 1)
			}
			CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let StaticValue::Num(n) = scrutinee.stage(environment) else { panic!() };
				(0..n).fold(case_nil.stage(environment), |previous, i| {
					case_suc.clone().stage_with(environment, [StaticValue::Num(i), previous])
				})
			}
			Bool => StaticValue::Type,
			BoolValue(b) => StaticValue::BoolValue(b),
			CaseBool { scrutinee, motive: _, case_false, case_true } => {
				let StaticValue::BoolValue(b) = scrutinee.stage(environment) else { panic!() };
				if b { case_true } else { case_false }.stage(environment)
			}
		}
	}
}

impl<const N: usize> Stage for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = Binder<Rc<DynamicValue>, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		self.mapv(|parameters, body| body.stage(&environment.bind(parameters)))
	}
}

impl Stage for DynamicTerm {
	type ObjectTerm = DynamicValue;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda(function) => DynamicValue::Function(function.stage(environment)),
			Pair { basepoint, fiberpoint } => DynamicValue::Pair {
				basepoint: rc!(basepoint.stage(environment)),
				fiberpoint: rc!(fiberpoint.stage(environment)),
			},
			Apply { scrutinee, argument } => DynamicValue::Apply {
				scrutinee: rc!(scrutinee.stage(environment)),
				argument: rc!(argument.stage(environment)),
			},
			Project(scrutinee, projection) =>
				DynamicValue::Project(rc!(scrutinee.stage(environment)), projection),
			Pi(base, family) => DynamicValue::Pi(rc!(base.stage(environment)), family.stage(environment)),
			Sigma(base, family) => DynamicValue::Sigma(rc!(base.stage(environment)), family.stage(environment)),
			Let { ty, argument, tail } => DynamicValue::Let {
				ty: rc!(ty.stage(environment)),
				argument: rc!(argument.stage(environment)),
				tail: tail.stage(environment),
			},
			Universe => DynamicValue::Universe,
			Splice(term) => {
				let StaticValue::Quote(value) = term.stage(environment) else { panic!() };
				value.as_ref().clone()
			}
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => DynamicValue::Suc(rc!(prev.stage(environment))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicValue::CaseNat {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_nil: rc!(case_nil.stage(environment)),
				case_suc: case_suc.stage(environment),
			},
			Bool => DynamicValue::Bool,
			BoolValue(b) => DynamicValue::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicValue::CaseBool {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_false: rc!(case_false.stage(environment)),
				case_true: rc!(case_true.stage(environment)),
			},
		}
	}
}

pub trait StageWith<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_with(self, environment: &Environment, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageWith<N> for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = StaticValue;
	fn stage_with(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage(&environment.extend(terms.map(Value::Static)))
	}
}

impl<const N: usize> StageWith<N> for Closure<Environment, StaticTerm, N> {
	type ObjectTerm = StaticValue;
	fn stage_with(self, _: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage(&self.environment.extend(terms.map(Value::Static)))
	}
}

pub trait Unstage {
	type CoreTerm;
	/// Transforms an object term into a core term.
	fn unstage(&self, context_len: Level) -> Self::CoreTerm;
}

impl<const N: usize> Unstage for Binder<Rc<DynamicValue>, N> {
	type CoreTerm = Binder<Box<DynamicTerm>, N>;
	fn unstage(&self, context_len: Level) -> Self::CoreTerm {
		self.map_ref(|body| bx!(body.unstage(context_len + N)))
	}
}

impl Unstage for DynamicValue {
	type CoreTerm = DynamicTerm;
	fn unstage(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use DynamicValue::*;
		match self {
			Variable(name, Level(variable)) => DynamicTerm::Variable(*name, Index(context_len - 1 - variable)),
			Function(function) => DynamicTerm::Lambda(function.unstage(level)),
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unstage(level)),
				fiberpoint: bx!(fiberpoint.unstage(level)),
			},
			Apply { scrutinee, argument } => DynamicTerm::Apply {
				scrutinee: bx!(scrutinee.unstage(level)),
				argument: bx!(argument.unstage(level)),
			},
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.unstage(level)), *projection),
			Pi(base, family) => DynamicTerm::Pi(bx!(base.unstage(level)), family.unstage(level)),
			Sigma(base, family) => DynamicTerm::Sigma(bx!(base.unstage(level)), family.unstage(level)),
			Let { ty, argument, tail } => DynamicTerm::Let {
				ty: bx!(ty.unstage(level)),
				argument: bx!(argument.unstage(level)),
				tail: tail.unstage(level),
			},
			Universe => DynamicTerm::Universe,
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.unstage(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_nil: bx!(case_nil.unstage(level)),
				case_suc: case_suc.unstage(level),
			},
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_false: bx!(case_false.unstage(level)),
				case_true: bx!(case_true.unstage(level)),
			},
		}
	}
}
