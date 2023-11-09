use std::{fmt::Display, rc::Rc};

use super::{
	common::{Index, Level},
	parser::{DynamicPreterm, StaticPreterm},
};
use crate::utility::{bx, rc};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
}

fn write_static_spine(term: &StaticTerm, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Apply { .. } => write!(f, "{term}"),
		_ => write_static_atom(term, f),
	}
}

fn write_static_atom(term: &StaticTerm, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(..) => write!(f, "{term}"),
		Lambda { .. } => write!(f, "{{{term}}}"),
		Apply { .. } => write!(f, "{{{term}}}"),
		Pi { .. } => write!(f, "{{{term}}}"),
		Let { .. } => write!(f, "{{{term}}}"),
		Universe => write!(f, "{term}"),
		Lift(_) => write!(f, "{term}"),
		Quote(_) => write!(f, "{term}"),
	}
}

impl Display for StaticTerm {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use StaticTerm::*;
		match self {
			Variable(Index(index)) => write!(f, "#{index}"),
			Lambda { parameter, body } => write!(f, "({parameter}) => {body}"),
			Apply { scrutinee, argument } => {
				write_static_spine(&scrutinee, f)?;
				write!(f, " ")?;
				write_static_atom(&argument, f)
			}
			Pi { parameter, base, family } => write!(f, "({parameter} : {base}) -> {family}"),
			Let { assignee, ty, argument, tail } => write!(f, "@let {assignee} : {ty} = {argument}; {tail}"),
			Universe => write!(f, "@type"),
			Lift(liftee) => {
				write!(f, "^")?;
				write_dynamic_atom(liftee, f)
			}
			Quote(quotee) => write!(f, "[{quotee}]"),
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Splice(Box<StaticTerm>),
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } => write!(f, "{term}"),
		_ => write_dynamic_atom(term, f),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) => write!(f, "{term}"),
		Lambda { .. } => write!(f, "{{{term}}}"),
		Apply { .. } => write!(f, "{{{term}}}"),
		Pi { .. } => write!(f, "{{{term}}}"),
		Let { .. } => write!(f, "{{{term}}}"),
		Universe => write!(f, "{term}"),
		Splice(_) => write!(f, "{term}"),
	}
}

impl Display for DynamicTerm {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		use DynamicTerm::*;
		match self {
			Variable(Index(index)) => write!(f, "#{index}"),
			Lambda { parameter, body } => write!(f, "({parameter}) => {body}"),
			Apply { scrutinee, argument } => {
				write_dynamic_spine(&scrutinee, f)?;
				write!(f, " ")?;
				write_dynamic_atom(&argument, f)
			}
			Pi { parameter, base, family } => write!(f, "({parameter} : {base}) -> {family}"),
			Let { assignee, ty, argument, tail } => write!(f, "@let {assignee} : {ty} = {argument}; {tail}"),
			Universe => write!(f, "@type"),
			Splice(splicee) => write!(f, "[{splicee}]"),
		}
	}
}

#[derive(Clone)]
pub enum StaticNeutral {
	Variable(Level),
	Apply { callee: Rc<Self>, argument: Rc<StaticValue> },
}

#[derive(Clone)]
pub enum StaticValue {
	Neutral(StaticNeutral),
	Universe,
	Lift(DynamicValue),
	Quote(DynamicValue),
	IndexedProduct(Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Rc<dyn Fn(Self) -> Self>),
}

#[derive(Clone)]
pub enum DynamicNeutral {
	Variable(Level),
	Apply { callee: Rc<Self>, argument: Rc<DynamicValue> },
	Splice(StaticNeutral),
}

#[derive(Clone)]
pub enum DynamicValue {
	Neutral(DynamicNeutral),
	Universe,
	IndexedProduct(Rc<Self>, Rc<dyn Fn(Self) -> Self>),
	Function(Rc<dyn Fn(Self) -> Self>),
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
	tys: Vec<(String, Value)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.0.len())
	}

	#[must_use]
	pub fn bind_static(mut self, name: String, ty: StaticValue) -> Self {
		self.environment.push(Value::Static(StaticValue::Neutral(StaticNeutral::Variable(self.len()))));
		self.tys.push((name, Value::Static(ty)));
		self
	}

	#[must_use]
	pub fn bind_dynamic(mut self, name: String, ty: DynamicValue) -> Self {
		self.environment.push(Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(self.len()))));
		self.tys.push((name, Value::Dynamic(ty)));
		self
	}

	#[must_use]
	pub fn extend(mut self, name: String, ty: Value, value: Value) -> Self {
		self.environment.0.push(value);
		self.tys.push((name, ty));
		self
	}
}

fn reify_static_open_neutral(neutral: &StaticNeutral, level @ Level(context_length): Level) -> StaticTerm {
	use StaticNeutral::*;
	match neutral {
		Variable(Level(level)) => StaticTerm::Variable(Index(context_length - 1 - level)),
		Apply { callee, argument } => StaticTerm::Apply {
			scrutinee: bx!(reify_static_open_neutral(callee, level)),
			argument: bx!(reify_static_open_value(&argument, level)),
		},
	}
}

fn reify_static_open_value(value: &StaticValue, level: Level) -> StaticTerm {
	use StaticValue::*;
	match value {
		Neutral(neutral) => reify_static_open_neutral(neutral, level),
		Universe => StaticTerm::Universe,
		IndexedProduct(base, family) => StaticTerm::Pi {
			parameter: "_".to_owned(),
			base: bx!(reify_static_open_value(base, level)),
			family: bx!(reify_static_open_value(
				&family(StaticValue::Neutral(StaticNeutral::Variable(level))),
				level.suc()
			)),
		},
		Function(function) => StaticTerm::Lambda {
			parameter: "_".to_owned(),
			body: bx!(reify_static_open_value(
				&function(StaticValue::Neutral(StaticNeutral::Variable(level))),
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
		Variable(Level(level)) => DynamicTerm::Variable(Index(context_length - 1 - level)),
		Apply { callee, argument } => DynamicTerm::Apply {
			scrutinee: bx!(reify_dynamic_open_neutral(callee, level)),
			argument: bx!(reify_dynamic_open_value(&argument, level)),
		},
		Splice(splicee) => DynamicTerm::Splice(bx!(reify_static_open_neutral(splicee, level))),
	}
}

fn reify_dynamic_open_value(value: &DynamicValue, level: Level) -> DynamicTerm {
	use DynamicValue::*;
	match value {
		Neutral(neutral) => reify_dynamic_open_neutral(neutral, level),
		Universe => DynamicTerm::Universe,
		IndexedProduct(base, family) => DynamicTerm::Pi {
			parameter: "_".to_owned(),
			base: bx!(reify_dynamic_open_value(base, level)),
			family: bx!(reify_dynamic_open_value(
				&family(DynamicValue::Neutral(DynamicNeutral::Variable(level))),
				level.suc()
			)),
		},
		Function(function) => DynamicTerm::Lambda {
			parameter: "_".to_owned(),
			body: bx!(reify_dynamic_open_value(
				&function(DynamicValue::Neutral(DynamicNeutral::Variable(level))),
				level.suc()
			)),
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
						Some((StaticTerm::Variable(Index(i)), ty.clone()))
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
			let StaticValue::IndexedProduct(base, family) = scrutinee_ty else { panic!() };
			let argument = verify_static(context, *argument, (*base).clone());
			let argument_value = evaluate_static(&context.environment, argument.clone());
			(StaticTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument) }, family(argument_value))
		}
		Universe => (StaticTerm::Universe, StaticValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = evaluate_static(&context.environment, base.clone());
			let family = verify_static(
				&context.clone().bind_static(parameter.clone(), base_value),
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
				&context.clone().extend(assignee.clone(), Value::Static(ty_value), Value::Static(argument_value)),
				*tail,
			);
			(
				StaticTerm::Let { assignee: assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) },
				tail_ty,
			)
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
		(Lambda { parameter, body }, StaticValue::IndexedProduct(base, family)) => {
			let body = verify_static(
				&context.clone().bind_static(parameter.clone(), base.as_ref().clone()),
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
				&context.clone().extend(
					assignee.clone(),
					Value::Static(ty_value.clone()),
					Value::Static(argument_value),
				),
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
						Some((DynamicTerm::Variable(Index(i)), ty.clone()))
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
			let (scrutinee, scrutinee_ty) = synthesize_dynamic(context, *scrutinee);
			let DynamicValue::IndexedProduct(base, family) = scrutinee_ty else { panic!() };
			let argument = verify_dynamic(context, *argument, (*base).clone());
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			(DynamicTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument) }, family(argument_value))
		}
		Universe => (DynamicTerm::Universe, DynamicValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_dynamic(context, *base, DynamicValue::Universe);
			let base_value = evaluate_dynamic(&context.environment, base.clone());
			let family = verify_dynamic(
				&context.clone().bind_dynamic(parameter.clone(), base_value),
				*family,
				DynamicValue::Universe,
			);
			(DynamicTerm::Pi { parameter, base: bx!(base), family: bx!(family) }, DynamicValue::Universe)
		}
		Let { assignee, ty, argument, tail } => {
			let ty = verify_dynamic(context, *ty, DynamicValue::Universe);
			let ty_value = evaluate_dynamic(&context.environment, ty.clone());
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			let (tail, tail_ty) = synthesize_dynamic(
				&context.clone().extend(
					assignee.clone(),
					Value::Dynamic(ty_value),
					Value::Dynamic(argument_value),
				),
				*tail,
			);
			(
				DynamicTerm::Let { assignee: assignee, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) },
				tail_ty,
			)
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
		(Lambda { parameter, body }, DynamicValue::IndexedProduct(base, family)) => {
			let body = verify_dynamic(
				&context.clone().bind_dynamic(parameter.clone(), base.as_ref().clone()),
				*body,
				family(base.as_ref().clone()),
			);
			DynamicTerm::Lambda { parameter, body: bx!(body) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let ty = verify_dynamic(context, *ty, DynamicValue::Universe);
			let ty_value = evaluate_dynamic(&context.environment, ty.clone());
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			let argument_value = evaluate_dynamic(&context.environment, argument.clone());
			let tail = verify_dynamic(
				&context.clone().extend(
					assignee.clone(),
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
		Variable(index) => environment.lookup_static(index),
		Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			StaticValue::Function(rc!(move |value| {
				evaluate_static(&environment.extend(Value::Static(value)), body.clone())
			}))
		}
		Apply { scrutinee, argument } => {
			let argument = evaluate_static(environment, *argument);
			match evaluate_static(environment, *scrutinee) {
				StaticValue::Function(closure) => closure(argument),
				StaticValue::Neutral(neutral) =>
					StaticValue::Neutral(StaticNeutral::Apply { callee: rc!(neutral), argument: rc!(argument) }),
				_ => panic!(),
			}
		}
		Pi { base, family, .. } => StaticValue::IndexedProduct(
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

fn evaluate_dynamic(environment: &Environment, term: DynamicTerm) -> DynamicValue {
	use DynamicTerm::*;
	match term {
		Variable(index) => environment.lookup_dynamic(index),
		Lambda { body, .. } => {
			let environment = environment.clone();
			let body = *body;
			DynamicValue::Function(Rc::new(move |value| {
				evaluate_dynamic(&environment.extend(Value::Dynamic(value)), body.clone())
			}))
		}
		Apply { scrutinee, argument } => {
			let argument = evaluate_dynamic(environment, *argument);
			match evaluate_dynamic(environment, *scrutinee) {
				DynamicValue::Function(closure) => closure(argument),
				DynamicValue::Neutral(neutral) =>
					DynamicValue::Neutral(DynamicNeutral::Apply { callee: rc!(neutral), argument: rc!(argument) }),
				_ => panic!(),
			}
		}
		Pi { base, family, .. } => DynamicValue::IndexedProduct(
			rc!(evaluate_dynamic(environment, *base)),
			rc!({
				let environment = environment.clone();
				let family = *family;
				move |value| evaluate_dynamic(&environment.extend(Value::Dynamic(value)), family.clone())
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
	match (left, right) {
		(StaticValue::Universe, StaticValue::Universe) => true,
		(StaticValue::Lift(left), StaticValue::Lift(right)) =>
			is_convertible_dynamic(context_length, left, right),
		(StaticValue::Quote(left), StaticValue::Quote(right)) =>
			is_convertible_dynamic(context_length, left, right),
		(StaticValue::Neutral(left), StaticValue::Neutral(right)) =>
			is_convertible_static_neutral(context_length, left, right),
		(StaticValue::Function(left), StaticValue::Function(right)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
			&right(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
		),
		(left @ StaticValue::Neutral(_), StaticValue::Function(right)) => is_convertible_static(
			context_length.suc(),
			left,
			&right(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
		),
		(StaticValue::Function(left), right @ StaticValue::Neutral(_)) => is_convertible_static(
			context_length.suc(),
			&left(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
			right,
		),
		(
			StaticValue::IndexedProduct(left_base, left_family),
			StaticValue::IndexedProduct(right_base, right_family),
		) =>
			is_convertible_static(context_length, &left_base, &right_base)
				&& is_convertible_static(
					context_length.suc(),
					&left_family(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
					&right_family(StaticValue::Neutral(StaticNeutral::Variable(context_length))),
				),
		_ => false,
	}
}

pub fn is_convertible_static_neutral(
	context_length: Level,
	left: &StaticNeutral,
	right: &StaticNeutral,
) -> bool {
	match (left, right) {
		(StaticNeutral::Variable(left), StaticNeutral::Variable(right)) => left == right,
		(
			StaticNeutral::Apply { callee: left, argument: left_argument },
			StaticNeutral::Apply { callee: right, argument: right_argument },
		) =>
			is_convertible_static_neutral(context_length, left, right)
				&& is_convertible_static(context_length, left_argument.as_ref(), right_argument.as_ref()),
		_ => false,
	}
}

pub fn is_convertible_dynamic(context_length: Level, left: &DynamicValue, right: &DynamicValue) -> bool {
	match (left, right) {
		(DynamicValue::Universe, DynamicValue::Universe) => true,
		(DynamicValue::Neutral(left), DynamicValue::Neutral(right)) =>
			is_convertible_dynamic_neutral(context_length, left, right),
		(DynamicValue::Function(left), DynamicValue::Function(right)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
		),
		(left @ DynamicValue::Neutral(_), DynamicValue::Function(right)) => is_convertible_dynamic(
			context_length.suc(),
			left,
			&right(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
		),
		(DynamicValue::Function(left), right @ DynamicValue::Neutral(_)) => is_convertible_dynamic(
			context_length.suc(),
			&left(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
			right,
		),
		(
			DynamicValue::IndexedProduct(left_base, left_family),
			DynamicValue::IndexedProduct(right_base, right_family),
		) =>
			is_convertible_dynamic(context_length, &left_base, &right_base)
				&& is_convertible_dynamic(
					context_length.suc(),
					&left_family(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
					&right_family(DynamicValue::Neutral(DynamicNeutral::Variable(context_length))),
				),
		_ => false,
	}
}

pub fn is_convertible_dynamic_neutral(
	context_length: Level,
	left: &DynamicNeutral,
	right: &DynamicNeutral,
) -> bool {
	match (left, right) {
		(DynamicNeutral::Variable(left), DynamicNeutral::Variable(right)) => left == right,
		(
			DynamicNeutral::Apply { callee: left, argument: left_argument },
			DynamicNeutral::Apply { callee: right, argument: right_argument },
		) =>
			is_convertible_dynamic_neutral(context_length, left, right)
				&& is_convertible_dynamic(context_length, left_argument.as_ref(), right_argument.as_ref()),
		(DynamicNeutral::Splice(left), DynamicNeutral::Splice(right)) =>
			is_convertible_static_neutral(context_length, left, right),
		_ => false,
	}
}
