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
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Splice(Box<StaticTerm>),
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: Name, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Project { scrutinee: Box<Self>, projection: Projection },
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } | Project { .. } => write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe | Splice(_) => write_dynamic(term, f, interner),
		Lambda { .. } | Pair { .. } | Apply { .. } | Project { .. } | Pi { .. } | Sigma { .. } | Let { .. } => {
			write!(f, "(")?;
			write_dynamic(term, f, interner)?;
			write!(f, ")")
		}
	}
}

pub fn write_dynamic(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(name, ..) => write!(f, "{}", interner.resolve(name)),
		Lambda { parameter, body } => {
			write!(f, "|{}| ", interner.resolve(parameter))?;
			write_dynamic(body, f, interner)
		}
		Pair { basepoint, fiberpoint } => {
			write_dynamic_spine(basepoint, f, interner)?;
			write!(f, ", ")?;
			write_dynamic_spine(fiberpoint, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}
		Project { scrutinee, projection } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			match projection {
				Projection::Base => write!(f, "/."),
				Projection::Fiber => write!(f, "/!"),
			}
		}
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
		Let { assignee, ty, argument, tail } => {
			write!(f, "let {} : ", interner.resolve(assignee))?;
			write_dynamic(ty, f, interner)?;
			write!(f, " = ")?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(tail, f, interner)
		}
		Universe => write!(f, "*"),
		Splice(splicee) => {
			write!(f, "[")?;
			write_static(splicee, f, interner)?;
			write!(f, "]")
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
	Apply(Rc<Self>, Rc<DynamicValue>),
	Project(Rc<Self>, Projection),
	Splice(StaticNeutral),
}

#[derive(Clone)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe,
	IndexedProduct(Name, Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Name, Rc<dyn Fn(Self) -> Self>),
	IndexedSum(Name, Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Pair(/* basepoint */ Rc<Self>, /* fiberpoint */ Rc<Self>),
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
		Apply(callee, argument) => DynamicTerm::Apply {
			scrutinee: bx!(reify_dynamic_open_neutral(callee, level)),
			argument: bx!(reify_dynamic_open_value(argument, level)),
		},
		Project(scrutinee, projection) => DynamicTerm::Project {
			scrutinee: bx!(reify_dynamic_open_neutral(scrutinee, level)),
			projection: *projection,
		},
		Splice(splicee) => DynamicTerm::Splice(bx!(reify_static_open_neutral(splicee, level))),
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
				panic!()
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
		_ => false,
	}
}
