use std::{fmt::Debug, rc::Rc};

use super::{
	common::{Index, Level, Projection},
	elaborator::{DynamicTerm, StaticTerm},
	parser::Name,
};
use crate::utility::{bx, rc};

#[derive(Clone)]
pub enum StaticValue {
	Type,
	Quote(Rc<DynamicValue>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

impl Debug for StaticValue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Type => write!(f, "Type"),
			Self::Quote(quotee) => f.debug_tuple("Quote").field(quotee).finish(),
			Self::Function(_) => f.debug_tuple("Function").field(&format_args!("_")).finish(),
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicValue {
	Variable(Name, Level),
	Let {
		assignee: Name,
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Rc<Self>,
	},
	Universe,
	Pi {
		parameter: Name,
		base: Rc<Self>,
		family: Rc<Self>,
	},
	Function {
		parameter: Name,
		closure: Rc<Self>,
	},
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<Self>,
	},
	Sigma {
		parameter: Name,
		base: Rc<Self>,
		family: Rc<Self>,
	},
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	Project {
		scrutinee: Rc<Self>,
		projection: Projection,
	},
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive_parameter: Name,
		motive: Rc<Self>,
		case_nil: Rc<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Rc<Self>,
	},
}

impl DynamicValue {
	pub fn unstage(&self) -> super::elaborator::DynamicTerm {
		fn unstage_open(
			value: &DynamicValue,
			level @ Level(context_length): Level,
		) -> super::elaborator::DynamicTerm {
			use DynamicValue::*;
			match value {
				Variable(name, Level(variable)) =>
					DynamicTerm::Variable(*name, Index(context_length - 1 - variable)),
				Function { parameter, closure } =>
					DynamicTerm::Lambda { parameter: *parameter, body: bx!(unstage_open(closure, level.suc())) },
				Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
					basepoint: bx!(unstage_open(basepoint, level)),
					fiberpoint: bx!(unstage_open(fiberpoint, level)),
				},
				Apply { scrutinee, argument } => DynamicTerm::Apply {
					scrutinee: bx!(unstage_open(scrutinee, level)),
					argument: bx!(unstage_open(argument, level)),
				},
				Project { scrutinee, projection } => DynamicTerm::Project {
					scrutinee: bx!(unstage_open(scrutinee, level)),
					projection: *projection,
				},
				Pi { parameter, base, family } => DynamicTerm::Pi {
					parameter: *parameter,
					base: bx!(unstage_open(base, level)),
					family: bx!(unstage_open(family, level.suc())),
				},
				Sigma { parameter, base, family } => DynamicTerm::Sigma {
					parameter: *parameter,
					base: bx!(unstage_open(base, level)),
					family: bx!(unstage_open(family, level.suc())),
				},
				Let { assignee, ty, argument, tail } => DynamicTerm::Let {
					assignee: *assignee,
					ty: bx!(unstage_open(ty, level)),
					argument: bx!(unstage_open(argument, level)),
					tail: bx!(unstage_open(tail, level.suc())),
				},
				Universe => DynamicTerm::Universe,
				Nat => DynamicTerm::Nat,
				Num(n) => DynamicTerm::Num(*n),
				Suc(prev) => DynamicTerm::Suc(bx!(unstage_open(prev, level))),
				CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } =>
					DynamicTerm::CaseNat {
						scrutinee: bx!(unstage_open(scrutinee, level)),
						motive_parameter: *motive_parameter,
						motive: bx!(unstage_open(motive, level.suc())),
						case_nil: bx!(unstage_open(case_nil, level)),
						case_suc_parameters: *case_suc_parameters,
						case_suc: bx!(unstage_open(case_suc, level.suc().suc())),
					},
			}
		}

		unstage_open(self, Level(0))
	}
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
	pub fn extend_static(&self, value: StaticValue) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Static(value));
		environment
	}

	#[must_use]
	pub fn extend_dynamic(&self, name: Name) -> Self {
		let mut environment = self.clone();
		environment.values.push(Value::Dynamic(name, self.dynamic_context_length));
		environment.dynamic_context_length = environment.dynamic_context_length.suc();
		environment
	}
}

pub fn evaluate_static(environment: &Environment, term: StaticTerm) -> StaticValue {
	use StaticTerm::*;
	match term {
		Variable(_, index) => environment.lookup_static(index),
		Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			StaticValue::Function(Rc::new(move |value| {
				evaluate_static(&environment.extend_static(value), body.clone())
			}))
		}
		Apply { scrutinee, argument } => {
			let StaticValue::Function(closure) = evaluate_static(environment, *scrutinee) else { panic!() };
			let argument = evaluate_static(environment, *argument);
			closure(argument)
		}
		Pi { .. } => StaticValue::Type,
		Let { argument, tail, .. } =>
			evaluate_static(&environment.extend_static(evaluate_static(environment, *argument)), *tail),
		Universe => StaticValue::Type,
		Lift(_) => StaticValue::Type,
		Quote(term) => StaticValue::Quote(rc!(evaluate_dynamic(environment, *term))),
	}
}

pub fn stage(term: DynamicTerm) -> DynamicValue {
	evaluate_dynamic(&Environment::new(), term)
}

pub fn evaluate_dynamic(environment: &Environment, term: DynamicTerm) -> DynamicValue {
	use DynamicTerm::*;
	match term {
		Variable(_, index) => environment.lookup_dynamic(index),
		Lambda { parameter, body } => DynamicValue::Function {
			parameter,
			closure: rc!(evaluate_dynamic(&environment.extend_dynamic(parameter), *body)),
		},
		Pair { basepoint, fiberpoint } => DynamicValue::Pair {
			basepoint: rc!(evaluate_dynamic(environment, *basepoint)),
			fiberpoint: rc!(evaluate_dynamic(environment, *fiberpoint)),
		},
		Apply { scrutinee, argument } => DynamicValue::Apply {
			scrutinee: rc!(evaluate_dynamic(environment, *scrutinee)),
			argument: rc!(evaluate_dynamic(environment, *argument)),
		},
		Project { scrutinee, projection } =>
			DynamicValue::Project { scrutinee: rc!(evaluate_dynamic(environment, *scrutinee)), projection },
		Pi { parameter, base, family } => DynamicValue::Pi {
			parameter,
			base: rc!(evaluate_dynamic(environment, *base)),
			family: rc!(evaluate_dynamic(&environment.extend_dynamic(parameter), *family)),
		},
		Sigma { parameter, base, family } => DynamicValue::Sigma {
			parameter,
			base: rc!(evaluate_dynamic(environment, *base)),
			family: rc!(evaluate_dynamic(&environment.extend_dynamic(parameter), *family)),
		},
		Let { assignee, ty, argument, tail } => DynamicValue::Let {
			assignee,
			ty: rc!(evaluate_dynamic(environment, *ty)),
			argument: rc!(evaluate_dynamic(environment, *argument)),
			tail: rc!(evaluate_dynamic(&environment.extend_dynamic(assignee), *tail)),
		},
		Universe => DynamicValue::Universe,
		Splice(term) => {
			let StaticValue::Quote(value) = evaluate_static(environment, *term) else { panic!() };
			value.as_ref().clone()
		}
		Nat => DynamicValue::Nat,
		Num(n) => DynamicValue::Num(n),
		Suc(prev) => DynamicValue::Suc(rc!(evaluate_dynamic(environment, *prev))),
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } =>
			DynamicValue::CaseNat {
				scrutinee: rc!(evaluate_dynamic(environment, *scrutinee)),
				motive_parameter,
				motive: rc!(evaluate_dynamic(&environment.extend_dynamic(motive_parameter), *motive)),
				case_nil: rc!(evaluate_dynamic(environment, *case_nil)),
				case_suc_parameters,
				case_suc: rc!(evaluate_dynamic(
					&environment.extend_dynamic(case_suc_parameters.0).extend_dynamic(case_suc_parameters.1),
					*case_suc
				)),
			},
	}
}
