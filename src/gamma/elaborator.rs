use std::{fmt::Write, rc::Rc};

use lasso::Rodeo;

use super::{
	common::{Index, Level, Projection},
	parser::{DynamicPreterm, Name, StaticPreterm},
};
use crate::utility::{bx, rc};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Name, Index),
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: Name, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
}

fn write_static_spine(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Apply { .. } => write_static(term, f, interner),
		_ => write_static_atom(term, f, interner),
	}
}

fn write_static_atom(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(..) | Universe | Lift(_) | Quote(_) => write_static(term, f, interner),
		Lambda { .. } | Apply { .. } | Pi { .. } | Let { .. } => {
			write!(f, "(")?;
			write_static(term, f, interner)?;
			write!(f, ")")
		}
	}
}

fn write_static(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(name, ..) => write!(f, "{}", interner.resolve(name)),
		Lambda { parameter, body } => {
			write!(f, "|{}| ", interner.resolve(parameter))?;
			write_static(body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_static_atom(argument, f, interner)
		}
		Pi { parameter, base, family } => {
			let parameter = interner.resolve(parameter);
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_static(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_static(base, f, interner)?;
				write!(f, " -> ")?;
			}
			write_static(family, f, interner)
		}
		Let { assignee, ty, argument, tail } => {
			write!(f, "let {} : ", interner.resolve(assignee))?;
			write_static(ty, f, interner)?;
			write!(f, " = ")?;
			write_static(argument, f, interner)?;
			write!(f, "; ")?;
			write_static(tail, f, interner)
		}
		Universe => write!(f, "*"),
		Lift(liftee) => {
			write!(f, "'")?;
			write_dynamic_atom(liftee, f, interner)
		}
		Quote(quotee) => {
			write!(f, "[")?;
			write_dynamic(quotee, f, interner)?;
			write!(f, "]")
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Name, Index),
	Let {
		assignee: Name,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Box<Self>,
	},
	Splice(Box<StaticTerm>),
	Universe,
	Pi {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Lambda {
		parameter: Name,
		body: Box<Self>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project {
		scrutinee: Box<Self>,
		projection: Projection,
	},
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive_parameter: Name,
		motive: Box<Self>,
		case_nil: Box<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Box<Self>,
	},
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } | Project { .. } | Suc(..) | CaseNat { .. } => write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe | Splice(_) | Nat | Num(..) => write_dynamic(term, f, interner),
		Let { .. }
		| Lambda { .. }
		| Pair { .. }
		| Apply { .. }
		| Project { .. }
		| Pi { .. }
		| Sigma { .. }
		| Suc(..)
		| CaseNat { .. } => {
			write!(f, "(")?;
			write_dynamic(term, f, interner)?;
			write!(f, ")")
		}
	}
}

pub fn write_dynamic(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Let { assignee, ty, argument, tail } => {
			write!(f, "let {} : ", interner.resolve(assignee))?;
			write_dynamic(ty, f, interner)?;
			write!(f, " = ")?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(tail, f, interner)
		}
		Variable(name, ..) => write!(f, "{}", interner.resolve(name)),
		Splice(splicee) => {
			write!(f, "[")?;
			write_static(splicee, f, interner)?;
			write!(f, "]")
		}
		Universe => write!(f, "*"),
		Pi { parameter, base, family } => {
			let parameter = interner.resolve(parameter);
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_dynamic(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_dynamic_spine(base, f, interner)?;
				write!(f, " -> ")?;
			}
			write_dynamic(family, f, interner)
		}
		Lambda { parameter, body } => {
			write!(f, "|{}| ", interner.resolve(parameter))?;
			write_dynamic(body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}
		Sigma { parameter, base, family } => {
			let parameter = interner.resolve(parameter);
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_dynamic(base, f, interner)?;
				write!(f, "| & ")?;
			} else {
				write_dynamic_spine(base, f, interner)?;
				write!(f, " & ")?;
			}
			write_dynamic(family, f, interner)
		}
		Pair { basepoint, fiberpoint } => {
			write_dynamic_spine(basepoint, f, interner)?;
			write!(f, ", ")?;
			write_dynamic_spine(fiberpoint, f, interner)
		}
		Project { scrutinee, projection } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			match projection {
				Projection::Base => write!(f, "/."),
				Projection::Fiber => write!(f, "/!"),
			}
		}
		Nat => write!(f, "nat"),
		Num(n) => write!(f, "{n}"),
		Suc(prev) => {
			write!(f, "suc ")?;
			write_dynamic_atom(prev, f, interner)
		}
		CaseNat { scrutinee, motive_parameter, motive: _, case_nil, case_suc_parameters, case_suc } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " :: |{}| ", interner.resolve(motive_parameter))?;
			// TODO: if we're printing this, we need to keep track of our context length when printing.
			write!(f, "?")?;
			//write_dynamic(motive, f, interner)?;
			write!(f, " {{nil -> ")?;
			write_dynamic_spine(case_nil, f, interner)?;
			write!(
				f,
				" | suc {} {} -> ",
				interner.resolve(&case_suc_parameters.0),
				interner.resolve(&case_suc_parameters.1)
			)?;
			write_dynamic_spine(case_suc, f, interner)?;
			write!(f, "}}")
		}
	}
}

#[derive(Clone)]
pub enum StaticNeutral {
	Variable(Name, Level),
	Apply(Rc<Self>, Rc<StaticValue>),
}

#[derive(Clone)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	Lift(DynamicValue),
	Quote(DynamicValue),
	IndexedProduct(Name, Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Name, Rc<dyn Fn(Self) -> Self>),
}

#[derive(Clone)]
pub enum DynamicNeutral {
	Variable(Name, Level),
	Splice(StaticNeutral),
	Apply(Rc<Self>, Rc<DynamicValue>),
	Project(Rc<Self>, Projection),
	CaseNat {
		scrutinee: Rc<Self>,
		motive_parameter: Name,
		motive: Rc<dyn Fn(DynamicValue) -> DynamicValue>,
		case_nil: Rc<DynamicValue>,
		case_suc_parameters: (Name, Name),
		case_suc: Rc<dyn Fn(DynamicValue, DynamicValue) -> DynamicValue>,
	},
	Suc(Rc<Self>),
}

#[derive(Clone)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe,
	IndexedProduct(Name, Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Name, Rc<dyn Fn(Self) -> Self>),
	IndexedSum(Name, Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
	Nat,
	Num(usize),
}

impl DynamicValue {
	pub fn reify(&self) -> DynamicTerm {
		reify_dynamic_open_value(self, Level(0))
	}
}

#[derive(Clone)]
pub enum Value {
	Static(StaticValue),
	Dynamic(DynamicValue),
}

#[derive(Clone)]
struct Environment(Vec<Value>);

impl Environment {
	fn lookup_static(&self, Index(i): Index) -> StaticValue {
		let Some(Value::Static(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	fn lookup_dynamic(&self, Index(i): Index) -> DynamicValue {
		let Some(Value::Dynamic(value)) = self.0.get(self.0.len() - 1 - i) else { panic!() };
		value.clone()
	}

	#[must_use]
	fn extend(&self, value: Value) -> Self {
		let mut environment = self.clone();
		environment.0.push(value);
		environment
	}

	fn push(&mut self, value: Value) {
		self.0.push(value);
	}
}

#[derive(Clone)]
pub struct Context {
	environment: Environment,
	tys: Vec<(Name, Value)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.0.len())
	}

	#[must_use]
	pub fn bind_static(mut self, name: Name, ty: StaticValue) -> Self {
		self.environment.push(Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))));
		self.tys.push((name, Value::Static(ty)));
		self
	}

	#[must_use]
	pub fn bind_dynamic(mut self, name: Name, ty: DynamicValue) -> Self {
		self
			.environment
			.push(Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))));
		self.tys.push((name, Value::Dynamic(ty)));
		self
	}

	#[must_use]
	pub fn extend(mut self, name: Name, ty: Value, value: Value) -> Self {
		self.environment.0.push(value);
		self.tys.push((name, ty));
		self
	}
}

fn reify_static_open_neutral(neutral: &StaticNeutral, level @ Level(context_length): Level) -> StaticTerm {
	use StaticNeutral::*;
	match neutral {
		Variable(name, Level(level)) => StaticTerm::Variable(*name, Index(context_length - 1 - level)),
		Apply(callee, argument) => StaticTerm::Apply {
			scrutinee: bx!(reify_static_open_neutral(callee, level)),
			argument: bx!(reify_static_open_value(argument, level)),
		},
	}
}

fn reify_static_open_value(value: &StaticValue, level: Level) -> StaticTerm {
	use StaticValue::*;
	match value {
		Neutral(neutral) => reify_static_open_neutral(neutral, level),
		Universe => StaticTerm::Universe,
		IndexedProduct(name, base, family) => StaticTerm::Pi {
			parameter: *name,
			base: bx!(reify_static_open_value(base, level)),
			family: bx!(reify_static_open_value(
				&family(StaticValue::Neutral(StaticNeutral::Variable(*name, level))),
				level.suc()
			)),
		},
		Function(name, function) => StaticTerm::Lambda {
			parameter: *name,
			body: bx!(reify_static_open_value(
				&function(StaticValue::Neutral(StaticNeutral::Variable(*name, level))),
				level.suc()
			)),
		},
		Lift(liftee) => StaticTerm::Lift(bx!(reify_dynamic_open_value(liftee, level))),
		Quote(quotee) => StaticTerm::Quote(bx!(reify_dynamic_open_value(quotee, level))),
	}
}

fn reify_dynamic_open_neutral(neutral: &DynamicNeutral, level @ Level(context_length): Level) -> DynamicTerm {
	use DynamicNeutral::*;
	match neutral {
		Variable(name, Level(level)) => DynamicTerm::Variable(*name, Index(context_length - 1 - level)),
		Splice(splicee) => DynamicTerm::Splice(bx!(reify_static_open_neutral(splicee, level))),
		Apply(callee, argument) => DynamicTerm::Apply {
			scrutinee: bx!(reify_dynamic_open_neutral(callee, level)),
			argument: bx!(reify_dynamic_open_value(argument, level)),
		},
		Project(scrutinee, projection) => DynamicTerm::Project {
			scrutinee: bx!(reify_dynamic_open_neutral(scrutinee, level)),
			projection: *projection,
		},
		Suc(prev) => DynamicTerm::Suc(bx!(reify_dynamic_open_neutral(prev, level))),
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } =>
			DynamicTerm::CaseNat {
				scrutinee: bx!(reify_dynamic_open_neutral(&scrutinee, level)),
				motive_parameter: *motive_parameter,
				motive: bx!(reify_dynamic_open_value(
					&motive(DynamicValue::Neutral(DynamicNeutral::Variable(*motive_parameter, level))),
					level.suc()
				)),
				case_nil: bx!(reify_dynamic_open_value(&case_nil, level)),
				case_suc_parameters: *case_suc_parameters,
				case_suc: bx!(reify_dynamic_open_value(
					&case_suc(
						DynamicValue::Neutral(Variable(case_suc_parameters.0, level)),
						DynamicValue::Neutral(Variable(case_suc_parameters.1, level.suc()))
					),
					level.suc().suc()
				)),
			},
	}
}

fn reify_dynamic_open_value(value: &DynamicValue, level: Level) -> DynamicTerm {
	use DynamicValue::*;
	match value {
		Neutral(neutral) => reify_dynamic_open_neutral(neutral, level),
		Universe => DynamicTerm::Universe,
		IndexedProduct(name, base, family) => DynamicTerm::Pi {
			parameter: *name,
			base: bx!(reify_dynamic_open_value(base, level)),
			family: bx!(reify_dynamic_open_value(
				&family(DynamicValue::Neutral(DynamicNeutral::Variable(*name, level))),
				level.suc()
			)),
		},
		Function(name, function) => DynamicTerm::Lambda {
			parameter: *name,
			body: bx!(reify_dynamic_open_value(
				&function(DynamicValue::Neutral(DynamicNeutral::Variable(*name, level))),
				level.suc()
			)),
		},
		IndexedSum(name, base, family) => DynamicTerm::Sigma {
			parameter: *name,
			base: bx!(reify_dynamic_open_value(base, level)),
			family: bx!(reify_dynamic_open_value(
				&family(DynamicValue::Neutral(DynamicNeutral::Variable(*name, level))),
				level.suc()
			)),
		},
		Pair(basepoint, fiberpoint) => DynamicTerm::Pair {
			basepoint: bx!(reify_dynamic_open_value(basepoint, level)),
			fiberpoint: bx!(reify_dynamic_open_value(fiberpoint, level)),
		},
		Nat => DynamicTerm::Nat,
		Num(n) => DynamicTerm::Num(*n),
	}
}

pub fn synthesize_static(context: &Context, term: StaticPreterm) -> (StaticTerm, StaticValue) {
	use StaticPreterm::*;
	match term {
		Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, ty))| {
				if &name == name_1 {
					if let Value::Static(ty) = ty {
						Some((StaticTerm::Variable(name, Index(i)), ty.clone()))
					} else {
						None
					}
				} else {
					None
				}
			})
			.unwrap(),
		Lambda { .. } => panic!(),
		Apply { scrutinee, argument } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
			let StaticValue::IndexedProduct(_, base, family) = scrutinee_ty else { panic!() };
			let argument = verify_static(context, *argument, (*base).clone());
			let argument_value = evaluate_static(&context.environment, argument.clone());
			(StaticTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument) }, family(argument_value))
		}
		Universe => (StaticTerm::Universe, StaticValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = evaluate_static(&context.environment, base.clone());
			let family = verify_static(
				&context.clone().bind_static(parameter, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Pi { parameter, base: bx!(base), family: bx!(family) }, StaticValue::Universe)
		}
		Let { assignee, ty, argument, tail } => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = evaluate_static(&context.environment, ty.clone());
			let argument = verify_static(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = evaluate_static(&context.environment, argument.clone());
			let (tail, tail_ty) = synthesize_static(
				&context.clone().extend(assignee, Value::Static(ty_value), Value::Static(argument_value)),
				*tail,
			);
			(StaticTerm::Let { assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) }, tail_ty)
		}
		Lift(liftee) => {
			// NOTE: Does verifying work when dynamic universes are indexed?
			let liftee = verify_dynamic(context, *liftee, DynamicValue::Universe);
			(StaticTerm::Lift(bx!(liftee)), StaticValue::Universe)
		}
		Quote(quotee) => {
			let (quotee, quotee_ty) = synthesize_dynamic(context, *quotee);
			(StaticTerm::Quote(bx!(quotee)), StaticValue::Lift(quotee_ty))
		}
	}
}

pub fn verify_static(context: &Context, term: StaticPreterm, ty: StaticValue) -> StaticTerm {
	use StaticPreterm::*;
	match (term, ty) {
		(Lambda { parameter, body }, StaticValue::IndexedProduct(_, base, family)) => {
			let body = verify_static(
				&context.clone().bind_static(parameter, base.as_ref().clone()),
				*body,
				family(base.as_ref().clone()),
			);
			StaticTerm::Lambda { parameter, body: bx!(body) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = evaluate_static(&context.environment, ty.clone());
			let argument = verify_static(context, *argument, ty_value.clone());
			let argument_value = evaluate_static(&context.environment, argument.clone());
			let tail = verify_static(
				&context.clone().extend(assignee, Value::Static(ty_value.clone()), Value::Static(argument_value)),
				*tail,
				ty_value,
			);
			StaticTerm::Let { assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) }
		}
		(Quote(quotee), StaticValue::Lift(liftee)) => {
			let quotee = verify_dynamic(context, *quotee, liftee);
			StaticTerm::Quote(bx!(quotee))
		}
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(context, term);
			if is_convertible_static(context.len(), &synthesized_ty, &ty) {
				term
			} else {
				panic!()
			}
		}
	}
}

pub fn elaborate_dynamic_closed(term: DynamicPreterm) -> (DynamicTerm, DynamicValue) {
	synthesize_dynamic(&Context::empty(), term)
}

pub fn synthesize_dynamic(context: &Context, term: DynamicPreterm) -> (DynamicTerm, DynamicValue) {
	use DynamicPreterm::*;
	match term {
		Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, ty))| {
				if &name == name_1 {
					if let Value::Dynamic(ty) = ty {
						Some((DynamicTerm::Variable(name, Index(i)), ty.clone()))
					} else {
						None
					}
				} else {
					None
				}
			})
			.unwrap(),
		Let { assignee, ty, argument, tail } => {
			let ty = verify_dynamic(context, *ty, DynamicValue::Universe);
			let ty_value = evaluate_dynamic(&context.environment, ty.clone());
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			let (tail, tail_ty) = synthesize_dynamic(
				&context.clone().extend(assignee, Value::Dynamic(ty_value), Value::Dynamic(argument_value)),
				*tail,
			);
			(DynamicTerm::Let { assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) }, tail_ty)
		}
		Splice(splicee) => {
			let (splicee, StaticValue::Lift(liftee)) = synthesize_static(context, *splicee) else { panic!() };
			(DynamicTerm::Splice(bx!(splicee)), liftee)
		}
		Lambda { .. } | Pair { .. } => panic!(),
		Apply { scrutinee, argument } => {
			let (scrutinee, scrutinee_ty) = synthesize_dynamic(context, *scrutinee);
			let DynamicValue::IndexedProduct(_, base, family) = scrutinee_ty else { panic!() };
			let argument = verify_dynamic(context, *argument, (*base).clone());
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			(DynamicTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument) }, family(argument_value))
		}
		Project(scrutinee, projection) => {
			let (scrutinee, scrutinee_ty) = synthesize_dynamic(context, *scrutinee);
			let DynamicValue::IndexedSum(_, base, family) = scrutinee_ty else { panic!() };
			match projection {
				Projection::Base =>
					(DynamicTerm::Project { scrutinee: bx!(scrutinee), projection }, base.as_ref().clone()),
				Projection::Fiber => {
					let basepoint =
						DynamicTerm::Project { scrutinee: bx!(scrutinee.clone()), projection: Projection::Base };
					let basepoint = evaluate_dynamic(&context.environment, basepoint);
					(DynamicTerm::Project { scrutinee: bx!(scrutinee), projection }, family(basepoint))
				}
			}
		}
		Universe => (DynamicTerm::Universe, DynamicValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_dynamic(context, *base, DynamicValue::Universe);
			let base_value = evaluate_dynamic(&context.environment, base.clone());
			let family = verify_dynamic(
				&context.clone().bind_dynamic(parameter, base_value),
				*family,
				DynamicValue::Universe,
			);
			(DynamicTerm::Pi { parameter, base: bx!(base), family: bx!(family) }, DynamicValue::Universe)
		}
		Sigma { parameter, base, family } => {
			let base = verify_dynamic(context, *base, DynamicValue::Universe);
			let base_value = evaluate_dynamic(&context.environment, base.clone());
			let family = verify_dynamic(
				&context.clone().bind_dynamic(parameter, base_value),
				*family,
				DynamicValue::Universe,
			);
			(DynamicTerm::Sigma { parameter, base: bx!(base), family: bx!(family) }, DynamicValue::Universe)
		}
		Nat => (DynamicTerm::Nat, DynamicValue::Universe),
		Num(n) => (DynamicTerm::Num(n), DynamicValue::Nat),
		Suc(prev) => {
			let prev = verify_dynamic(context, *prev, DynamicValue::Nat);
			if let DynamicTerm::Num(p) = prev {
				(DynamicTerm::Num(p + 1), DynamicValue::Nat)
			} else {
				(DynamicTerm::Suc(bx!(prev)), DynamicValue::Nat)
			}
		}
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } => {
			let scrutinee = verify_dynamic(context, *scrutinee, DynamicValue::Nat);
			let scrutinee_value = evaluate_dynamic(&context.environment, scrutinee.clone());
			let motive = verify_dynamic(
				&context.clone().bind_dynamic(motive_parameter, DynamicValue::Nat),
				*motive,
				DynamicValue::Universe,
			);
			let motive_value = rc!({
				let motive = motive.clone();
				let environment = context.environment.clone();
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), motive.clone())
			});
			let case_nil = verify_dynamic(context, *case_nil, motive_value(DynamicValue::Num(0)));
			// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
			let case_suc = verify_dynamic(
				&context.clone().bind_dynamic(case_suc_parameters.0, DynamicValue::Nat).bind_dynamic(
					case_suc_parameters.1,
					motive_value(DynamicValue::Neutral(DynamicNeutral::Variable(
						case_suc_parameters.0,
						context.len(),
					))),
				),
				*case_suc,
				motive_value(DynamicValue::Neutral(DynamicNeutral::Suc(rc!(DynamicNeutral::Variable(
					case_suc_parameters.0,
					context.len()
				))))),
			);
			(
				DynamicTerm::CaseNat {
					scrutinee: bx!(scrutinee),
					motive_parameter,
					motive: bx!(motive),
					case_nil: bx!(case_nil),
					case_suc_parameters,
					case_suc: bx!(case_suc),
				},
				motive_value(scrutinee_value),
			)
		}
	}
}

pub fn verify_dynamic(context: &Context, term: DynamicPreterm, ty: DynamicValue) -> DynamicTerm {
	use DynamicPreterm::*;
	match (term, ty) {
		(Lambda { parameter, body }, DynamicValue::IndexedProduct(_, base, family)) => {
			let body = verify_dynamic(
				&context.clone().bind_dynamic(parameter, base.as_ref().clone()),
				*body,
				family(base.as_ref().clone()),
			);
			DynamicTerm::Lambda { parameter, body: bx!(body) }
		}
		(Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum(_, base, family)) => {
			let basepoint = verify_dynamic(context, *basepoint, base.as_ref().clone());
			let basepoint_value = evaluate_dynamic(&context.environment, basepoint.clone());
			let fiberpoint = verify_dynamic(context, *fiberpoint, family(basepoint_value));
			DynamicTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let ty = verify_dynamic(context, *ty, DynamicValue::Universe);
			let ty_value = evaluate_dynamic(&context.environment, ty.clone());
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			let tail = verify_dynamic(
				&context.clone().extend(
					assignee,
					Value::Dynamic(ty_value.clone()),
					Value::Dynamic(argument_value),
				),
				*tail,
				ty_value,
			);
			DynamicTerm::Let { assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) }
		}
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_dynamic(context, term);
			if is_convertible_dynamic(context.len(), &synthesized_ty, &ty) {
				term
			} else {
				println!("{:#?}", term);
				panic!(
					"synthesized type {:#?} did not match expected type {:#?}",
					reify_dynamic_open_value(&synthesized_ty, context.len()),
					reify_dynamic_open_value(&ty, context.len()),
				);
			}
		}
	}
}

fn evaluate_static(environment: &Environment, term: StaticTerm) -> StaticValue {
	use StaticTerm::*;
	match term {
		Variable(_, index) => environment.lookup_static(index),
		Lambda { parameter, body, .. } => StaticValue::Function(
			parameter,
			rc!({
				let environment = environment.clone();
				move |value| evaluate_static(&environment.extend(Value::Static(value)), *body.clone())
			}),
		),
		Apply { scrutinee, argument } => {
			let argument = evaluate_static(environment, *argument);
			match evaluate_static(environment, *scrutinee) {
				StaticValue::Function(_, closure) => closure(argument),
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Apply(rc!(neutral), rc!(argument))),
				_ => panic!(),
			}
		}
		Pi { parameter, base, family, .. } => StaticValue::IndexedProduct(
			parameter,
			rc!(evaluate_static(environment, *base)),
			rc!({
				let environment = environment.clone();
				let family = *family;
				move |value| evaluate_static(&environment.extend(Value::Static(value)), family.clone())
			}),
		),
		Let { argument, tail, .. } =>
			evaluate_static(&environment.extend(Value::Static(evaluate_static(environment, *argument))), *tail),
		Universe => StaticValue::Universe,
		Lift(liftee) => StaticValue::Lift(evaluate_dynamic(environment, *liftee)),
		Quote(quotee) => StaticValue::Quote(evaluate_dynamic(environment, *quotee)),
	}
}

pub fn evaluate(term: DynamicTerm) -> DynamicValue {
	evaluate_dynamic(&Environment(Vec::new()), term)
}

fn evaluate_dynamic(environment: &Environment, term: DynamicTerm) -> DynamicValue {
	use DynamicTerm::*;
	match term {
		Variable(_, index) => environment.lookup_dynamic(index),
		Lambda { parameter, body, .. } => DynamicValue::Function(
			parameter,
			rc!({
				let environment = environment.clone();
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), *body.clone())
			}),
		),
		Pair { basepoint, fiberpoint } => DynamicValue::Pair(
			rc!(evaluate_dynamic(environment, *basepoint)),
			rc!(evaluate_dynamic(environment, *fiberpoint)),
		),
		Apply { scrutinee, argument } => {
			let argument = evaluate_dynamic(environment, *argument);
			match evaluate_dynamic(environment, *scrutinee) {
				DynamicValue::Function(_, closure) => closure(argument),
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Apply(rc!(neutral), rc!(argument))),
				_ => panic!(),
			}
		}
		Project { scrutinee, projection } => match evaluate_dynamic(environment, *scrutinee) {
			DynamicValue::Pair(basepoint, fiberpoint) => match projection {
				Projection::Base => basepoint.as_ref().clone(),
				Projection::Fiber => fiberpoint.as_ref().clone(),
			},
			DynamicValue::Neutral(neutral) =>
				DynamicValue::Neutral(DynamicNeutral::Project(rc!(neutral), projection)),
			_ => panic!(),
		},
		Pi { parameter, base, family, .. } => DynamicValue::IndexedProduct(
			parameter,
			rc!(evaluate_dynamic(environment, *base)),
			rc!({
				let environment = environment.clone();
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), *family.clone())
			}),
		),
		Sigma { parameter, base, family, .. } => DynamicValue::IndexedSum(
			parameter,
			rc!(evaluate_dynamic(environment, *base)),
			rc!({
				let environment = environment.clone();
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), *family.clone())
			}),
		),
		Let { argument, tail, .. } => evaluate_dynamic(
			&environment.extend(Value::Dynamic(evaluate_dynamic(environment, *argument))),
			*tail,
		),
		Universe => DynamicValue::Universe,
		Splice(splicee) => match evaluate_static(environment, *splicee) {
			StaticValue::Quote(quotee) => quotee,
			StaticValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Splice(neutral)),
			_ => panic!(),
		},
		Nat => DynamicValue::Nat,
		Num(n) => DynamicValue::Num(n),
		Suc(prev) => match evaluate_dynamic(environment, *prev) {
			DynamicValue::Neutral(neutral) => DynamicValue::Neutral(DynamicNeutral::Suc(rc!(neutral))),
			DynamicValue::Num(n) => DynamicValue::Num(n + 1),
			_ => panic!(),
		},
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } =>
			match evaluate_dynamic(environment, *scrutinee) {
				DynamicValue::Num(n) => {
					fn evaluate_case_nat(
						environment: &Environment,
						n: usize,
						case_nil: Box<DynamicTerm>,
						case_suc: Box<DynamicTerm>,
					) -> DynamicValue {
						match n {
							0 => evaluate_dynamic(environment, *case_nil),
							n => {
								let n = n - 1;
								evaluate_dynamic(
									&environment.extend(Value::Dynamic(DynamicValue::Num(n))).extend(Value::Dynamic(
										evaluate_case_nat(environment, n, case_nil.clone(), case_suc.clone()),
									)),
									*case_suc,
								)
							}
						}
					}
					evaluate_case_nat(environment, n, case_nil, case_suc)
				}
				DynamicValue::Neutral(neutral) => {
					fn evaluate_case_nat_neutral(
						environment: &Environment,
						neutral: &DynamicNeutral,
						motive_parameter: Name,
						motive: Rc<dyn Fn(DynamicValue) -> DynamicValue>,
						case_nil: Box<DynamicTerm>,
						case_suc_parameters: (Name, Name),
						case_suc: Box<DynamicTerm>,
					) -> DynamicValue {
						match neutral {
							DynamicNeutral::Suc(prev) => evaluate_dynamic(
								&environment
									.extend(Value::Dynamic(DynamicValue::Neutral(prev.as_ref().clone())))
									.extend(Value::Dynamic(evaluate_case_nat_neutral(
										environment,
										prev,
										motive_parameter,
										motive,
										case_nil,
										case_suc_parameters,
										case_suc.clone(),
									))),
								*case_suc,
							),
							neutral => DynamicValue::Neutral(DynamicNeutral::CaseNat {
								scrutinee: rc!(neutral.clone()),
								motive_parameter,
								motive,
								case_nil: rc!(evaluate_dynamic(environment, *case_nil)),
								case_suc_parameters,
								case_suc: rc!({
									let environment = environment.clone();
									move |value_0, value_1| {
										evaluate_dynamic(
											&environment.extend(Value::Dynamic(value_0)).extend(Value::Dynamic(value_1)),
											*case_suc.clone(),
										)
									}
								}),
							}),
						}
					}
					let motive_value = rc!({
						let motive = motive.clone();
						let environment = environment.clone();
						move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), *motive.clone())
					});
					evaluate_case_nat_neutral(
						environment,
						&neutral,
						motive_parameter,
						motive_value,
						case_nil,
						case_suc_parameters,
						case_suc,
					)
				}
				c => panic!("{:#?}", std::mem::discriminant(&c)),
			},
	}
}

pub fn is_convertible_static(context_length: Level, left: &StaticValue, right: &StaticValue) -> bool {
	use StaticValue::*;
	match (left, right) {
		(Universe, Universe) => true,
		(Lift(left), Lift(right)) => is_convertible_dynamic(context_length, left, right),
		(Quote(left), Quote(right)) => is_convertible_dynamic(context_length, left, right),
		(Neutral(left), Neutral(right)) => is_convertible_static_neutral(context_length, left, right),
		(Function(lp, left), Function(rp, right)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(*lp, context_length))),
			&right(StaticValue::Neutral(StaticNeutral::Variable(*rp, context_length))),
		),
		(left @ Neutral(_), Function(rp, right)) => is_convertible_static(
			context_length.suc(),
			left,
			&right(StaticValue::Neutral(StaticNeutral::Variable(*rp, context_length))),
		),
		(Function(lp, left), right @ Neutral(_)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(*lp, context_length))),
			right,
		),
		(IndexedProduct(lp, left_base, left_family), IndexedProduct(rp, right_base, right_family)) =>
			is_convertible_static(context_length, left_base, right_base)
				&& is_convertible_static(
					context_length.suc(),
					&left_family(StaticValue::Neutral(StaticNeutral::Variable(*lp, context_length))),
					&right_family(StaticValue::Neutral(StaticNeutral::Variable(*rp, context_length))),
				),
		_ => false,
	}
}

pub fn is_convertible_static_neutral(
	context_length: Level,
	left: &StaticNeutral,
	right: &StaticNeutral,
) -> bool {
	use StaticNeutral::*;
	match (left, right) {
		(Variable(_, left), Variable(_, right)) => left == right,
		(Apply(left, left_argument), Apply(right, right_argument)) =>
			is_convertible_static_neutral(context_length, left, right)
				&& is_convertible_static(context_length, left_argument.as_ref(), right_argument.as_ref()),
		_ => false,
	}
}

pub fn is_convertible_dynamic(context_length: Level, left: &DynamicValue, right: &DynamicValue) -> bool {
	use DynamicValue::*;
	match (left, right) {
		(Universe, Universe) => true,
		(Neutral(left), Neutral(right)) => is_convertible_dynamic_neutral(context_length, left, right),
		(Function(lp, left), Function(rp, right)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(*lp, context_length))),
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(*rp, context_length))),
		),
		(left @ Neutral(_), Function(rp, right)) => is_convertible_dynamic(
			context_length.suc(),
			left,
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(*rp, context_length))),
		),
		(Function(lp, left), right @ Neutral(_)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(*lp, context_length))),
			right,
		),
		(Pair(left_bp, left_fp), Pair(right_bp, right_fp)) =>
			is_convertible_dynamic(context_length, left_bp, right_bp)
				&& is_convertible_dynamic(context_length, left_fp, right_fp),
		(Neutral(left), Pair(right_bp, right_fp)) =>
			is_convertible_dynamic(
				context_length,
				&Neutral(DynamicNeutral::Project(rc!(left.clone()), Projection::Base)),
				right_bp,
			) && is_convertible_dynamic(
				context_length,
				&Neutral(DynamicNeutral::Project(rc!(left.clone()), Projection::Fiber)),
				right_fp,
			),
		(Pair(left_bp, left_fp), Neutral(right)) =>
			is_convertible_dynamic(
				context_length,
				left_bp,
				&Neutral(DynamicNeutral::Project(rc!(right.clone()), Projection::Base)),
			) && is_convertible_dynamic(
				context_length,
				left_fp,
				&Neutral(DynamicNeutral::Project(rc!(right.clone()), Projection::Fiber)),
			),
		(IndexedProduct(lp, left_base, left_family), IndexedProduct(rp, right_base, right_family)) =>
			is_convertible_dynamic(context_length, left_base, right_base)
				&& is_convertible_dynamic(
					context_length.suc(),
					&left_family(DynamicValue::Neutral(DynamicNeutral::Variable(*lp, context_length))),
					&right_family(DynamicValue::Neutral(DynamicNeutral::Variable(*rp, context_length))),
				),
		(IndexedSum(lp, left_base, left_family), IndexedSum(rp, right_base, right_family)) =>
			is_convertible_dynamic(context_length, left_base, right_base)
				&& is_convertible_dynamic(
					context_length.suc(),
					&left_family(DynamicValue::Neutral(DynamicNeutral::Variable(*lp, context_length))),
					&right_family(DynamicValue::Neutral(DynamicNeutral::Variable(*rp, context_length))),
				),
		(Nat, Nat) => true,
		(Num(left), Num(right)) => left == right,
		_ => false,
	}
}

pub fn is_convertible_dynamic_neutral(
	context_length: Level,
	left: &DynamicNeutral,
	right: &DynamicNeutral,
) -> bool {
	use DynamicNeutral::*;
	match (left, right) {
		(Variable(_, left), Variable(_, right)) => left == right,
		(Apply(left, left_argument), Apply(right, right_argument)) =>
			is_convertible_dynamic_neutral(context_length, left, right)
				&& is_convertible_dynamic(context_length, left_argument.as_ref(), right_argument.as_ref()),
		(Project(left, left_projection), Project(right, right_projection)) =>
			left_projection == right_projection && is_convertible_dynamic_neutral(context_length, left, right),
		(Splice(left), Splice(right)) => is_convertible_static_neutral(context_length, left, right),
		(Suc(left), Suc(right)) => is_convertible_dynamic_neutral(context_length, left, right),
		(
			CaseNat {
				scrutinee: left_scrutinee,
				motive_parameter: left_motive_parameter,
				motive: left_motive,
				case_nil: left_case_nil,
				case_suc_parameters: left_case_suc_parameters,
				case_suc: left_case_suc,
			},
			CaseNat {
				scrutinee: right_scrutinee,
				motive_parameter: right_motive_parameter,
				motive: right_motive,
				case_nil: right_case_nil,
				case_suc_parameters: right_case_suc_parameters,
				case_suc: right_case_suc,
			},
		) =>
			is_convertible_dynamic_neutral(context_length, &left_scrutinee, &right_scrutinee)
				&& is_convertible_dynamic(
					context_length.suc(),
					&left_motive(DynamicValue::Neutral(DynamicNeutral::Variable(
						*left_motive_parameter,
						context_length,
					))),
					&right_motive(DynamicValue::Neutral(DynamicNeutral::Variable(
						*right_motive_parameter,
						context_length,
					))),
				) && is_convertible_dynamic(context_length, &left_case_nil, &right_case_nil)
				&& is_convertible_dynamic(
					context_length.suc().suc(),
					&left_case_suc(
						DynamicValue::Neutral(DynamicNeutral::Variable(left_case_suc_parameters.0, context_length)),
						DynamicValue::Neutral(DynamicNeutral::Variable(left_case_suc_parameters.1, context_length)),
					),
					&right_case_suc(
						DynamicValue::Neutral(DynamicNeutral::Variable(
							right_case_suc_parameters.0,
							context_length,
						)),
						DynamicValue::Neutral(DynamicNeutral::Variable(
							right_case_suc_parameters.1,
							context_length,
						)),
					),
				),
		_ => false,
	}
}
