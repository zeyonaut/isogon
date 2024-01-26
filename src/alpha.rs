use std::rc::Rc;

use nom::{
	branch::alt,
	bytes::complete::tag,
	character::complete::{alpha1, alphanumeric1, multispace0},
	combinator::recognize,
	multi::many0,
	sequence::{delimited, pair, preceded, terminated},
	IResult,
};

use crate::{parse::*, utility::*};

pub fn run(line: &str) {
	let ("", term) = parse_term_eof(&line).unwrap() else {
		return;
	};
	println!("parsed.");
	let (term, ty) = synthesize(&Context::empty(), term).unwrap();
	println!("synthesized: {:?}", term);
	println!("synthesized type: {:?}", ty);
	let value = evaluate(Vec::new(), term);
	println!("evaluated: {:?}", value.as_ref());
}

pub type Name = String;

#[derive(Debug)]
pub enum RawEliminator {
	Apply { argument: RawTerm },
	ProjectBase,
	ProjectFiber,
}

// The raw syntax: the output of the parser and the input of the elaborator.
#[derive(Debug)]
pub enum RawTerm {
	Variable(Name),
	Lambda { parameter: Name, body: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Compute { scrutinee: Box<Self>, eliminators: Vec<RawEliminator> }, // This should have a positive number of eliminators.
	Universe, // We'll use type-in-type for convenience of implementation.
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
}

pub fn parse_term_eof(input: &str) -> IResult<&str, RawTerm> {
	terminated(parse_term, multispace0)(input)
}

fn parse_term(input: &str) -> IResult<&str, RawTerm> {
	alt((
		parse_lambda,
		parse_let,
		parse_explicit_sigma,
		parse_explicit_pi,
		parse_spine_or_implicit_sigma_or_implicit_pi_or_pair,
	))(input)
}

fn sym<T, Input, Error: nom::error::ParseError<Input>>(t: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
	Input: nom::InputTake + nom::InputTakeAtPosition + nom::Compare<T>,
	T: nom::InputLength + Clone,
	<Input as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
{
	move |input| preceded(multispace0, tag(t.clone()))(input)
}

fn parse_identifier(input: &str) -> IResult<&str, &str> {
	preceded(multispace0, recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))))(input)
}

fn parse_universe(input: &str) -> IResult<&str, RawTerm> {
	let (input, _) = sym("@type")(input)?;
	Ok((input, RawTerm::Universe))
}

fn parse_variable(input: &str) -> IResult<&str, RawTerm> {
	let (input, parsed) = parse_identifier(input)?;
	Ok((input, RawTerm::Variable(parsed.to_string())))
}

fn parse_atom(input: &str) -> IResult<&str, RawTerm> {
	alt((parse_universe, parse_variable, delimited(sym("{"), parse_term, sym("}"))))(input)
}

fn parse_vertebra(input: &str) -> IResult<&str, RawEliminator> {
	if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>(".")(input) {
		Ok((input, RawEliminator::ProjectBase))
	} else if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("!")(input) {
		Ok((input, RawEliminator::ProjectFiber))
	} else {
		let (input, right) = parse_atom(input)?;
		Ok((input, RawEliminator::Apply { argument: right }))
	}
}

fn parse_spine(input: &str) -> IResult<&str, RawTerm> {
	let (input, atom) = parse_atom(input)?;
	let mut eliminators = vec![];
	let (input, ()) =
		fold_many0_once(parse_vertebra, move || (), |(), eliminator| eliminators.push(eliminator))(input)?;
	Ok((
		input,
		if eliminators.is_empty() { atom } else { RawTerm::Compute { scrutinee: bx!(atom), eliminators } },
	))
}

fn parse_spine_or_implicit_sigma_or_implicit_pi_or_pair(input: &str) -> IResult<&str, RawTerm> {
	let (input, left) = parse_spine(input)?;
	if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("*")(input) {
		let (input, right) = parse_term(input)?;
		Ok((input, RawTerm::Sigma { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("->")(input) {
		let (input, right) = parse_term(input)?;
		Ok((input, RawTerm::Pi { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>(",")(input) {
		let (input, right) = parse_spine_or_implicit_sigma_or_implicit_pi_or_pair(input)?;
		Ok((input, RawTerm::Pair { basepoint: bx!(left), fiberpoint: bx!(right) }))
	} else {
		Ok((input, left))
	}
}

fn parse_lambda(input: &str) -> IResult<&str, RawTerm> {
	let (input, parameter) = delimited(sym("("), parse_identifier, sym(")"))(input)?;
	let (input, _) = sym("=>")(input)?;
	let (input, body) = parse_term(input)?;
	Ok((input, RawTerm::Lambda { parameter: parameter.to_string(), body: bx!(body) }))
}

fn parse_let(input: &str) -> IResult<&str, RawTerm> {
	let (input, _) = sym("@let")(input)?;
	let (input, assignee) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, ty) = parse_term(input)?;
	let (input, _) = sym("=")(input)?;
	let (input, argument) = parse_term(input)?;
	let (input, _) = sym(";")(input)?;
	let (input, tail) = parse_term(input)?;
	Ok((
		input,
		RawTerm::Let { assignee: assignee.to_string(), ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) },
	))
}

fn parse_explicit_pi(input: &str) -> IResult<&str, RawTerm> {
	let (input, _) = sym("(")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_term(input)?;
	let (input, _) = sym(")")(input)?;
	let (input, _) = sym("->")(input)?;
	let (input, family) = parse_term(input)?;
	Ok((input, RawTerm::Pi { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}

fn parse_explicit_sigma(input: &str) -> IResult<&str, RawTerm> {
	let (input, _) = sym("(")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_term(input)?;
	let (input, _) = sym(")")(input)?;
	let (input, _) = sym("*")(input)?;
	let (input, family) = parse_term(input)?;
	Ok((input, RawTerm::Sigma { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}
/*
	Expr: {...}
	Variables: a-zA-Z_[a-zA-Z0-9_]*
	Lambda: (Variable) => V...
	Universe: @type
	Pi: (Variable: Expr) -> Expr
	Let: @let x = 2; ...

*/

// de Bruijn index: zero is the newest bound parameter.
#[derive(Clone, PartialEq, Debug)]
pub struct Index(usize);

#[derive(Clone, Debug)]
pub enum Eliminator {
	Apply { argument: Term },
	ProjectBase,
	ProjectFiber,
}

// The core syntax: the output of the elaborator.
#[derive(Clone, Debug)]
pub enum Term {
	Variable(Index),
	Lambda { parameter: Name, body: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Compute { scrutinee: Box<Self>, eliminators: Vec<Eliminator> },
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
}

pub type Environment = Vec<Rc<Value>>;

#[derive(Clone, Debug)]
pub struct Closure(pub Environment, pub Term);

impl Closure {
	pub fn apply_value(self, argument: Rc<Value>) -> Rc<Value> {
		let Self(environment, body) = self;
		let mut environment = environment.clone();
		environment.push(argument);
		evaluate(environment, body)
	}
}

// de Bruijn level: zero is the oldest bound parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Level(usize);

impl Level {
	pub fn suc(self) -> Self {
		let Self(level) = self;
		Self(level + 1)
	}
}

#[derive(Clone, Debug)]
pub enum NeutralEliminator {
	Apply { argument: Rc<Value> },
	ProjectBase,
	ProjectFiber,
}

// The semantic domain (of values).
#[derive(Clone, Debug)]
pub enum Value {
	// A neutral form.
	Neutral { variable: Level, eliminators: Vec<NeutralEliminator> },
	Lambda { parameter: Name, body: Closure },
	Pair { basepoint: Rc<Self>, fiberpoint: Rc<Self> },
	Pi { parameter: Name, base: Rc<Self>, family: Closure },
	Sigma { parameter: Name, base: Rc<Self>, family: Closure },
	Universe,
}

impl Value {
	pub fn variable(variable: Level) -> Self {
		Self::Neutral { variable, eliminators: vec![] }
	}
}

#[derive(Clone)]
pub struct Context {
	environment: Environment,
	tys: Vec<(Name, Rc<Value>)>, // Most recent last
}

impl Context {
	pub fn empty() -> Self {
		Self { environment: Vec::new(), tys: Vec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.len())
	}

	pub fn bind(mut self, name: Name, ty: Rc<Value>) -> Self {
		self.environment.push(rc!(Value::variable(self.len())));
		self.tys.push((name, ty));
		self
	}

	pub fn extend(mut self, name: Name, ty: Rc<Value>, value: Rc<Value>) -> Self {
		self.environment.push(value);
		self.tys.push((name, ty));
		self
	}
}

// Bidirectional elaboration. Verify or synthesize the type of the term in the context.
pub fn verify(context: &Context, term: RawTerm, ty: Rc<Value>) -> Option<Term> {
	match (term, ty.as_ref()) {
		(RawTerm::Lambda { parameter, body }, Value::Pi { parameter: _, base, family }) => {
			let body = verify(
				&context.clone().bind(parameter.clone(), base.clone()),
				*body,
				family.clone().apply_value(rc!(Value::variable(context.len()))),
			)?;
			Some(Term::Lambda { parameter, body: bx!(body) })
		}
		(RawTerm::Pair { basepoint, fiberpoint }, Value::Sigma { parameter: _, base, family }) => {
			let basepoint = verify(context, *basepoint, base.clone())?;
			let basepoint_value = evaluate(context.environment.clone(), basepoint.clone());
			let fiberpoint = verify(context, *fiberpoint, family.clone().apply_value(basepoint_value))?;
			Some(Term::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) })
		}
		(RawTerm::Let { assignee, ty: argument_ty, argument, tail }, _) => {
			let argument_ty = verify(context, *argument_ty, rc!(Value::Universe))?;
			let argument_ty_value = evaluate(context.environment.clone(), argument_ty.clone());
			let argument = verify(context, *argument, argument_ty_value.clone())?;
			let argument_value = evaluate(context.environment.clone(), argument.clone());
			let tail =
				verify(&context.clone().extend(assignee.clone(), argument_ty_value, argument_value), *tail, ty)?;
			Some(Term::Let { assignee, ty: bx!(argument_ty), argument: bx!(argument), tail: bx!(tail) })
		}
		(term, _) => {
			let (term, synthesized_ty) = synthesize(context, term)?;
			if is_convertible(context.len(), synthesized_ty, ty) {
				Some(term)
			} else {
				None
			}
		}
	}
}

pub fn synthesize(context: &Context, term: RawTerm) -> Option<(Term, Rc<Value>)> {
	match term {
		RawTerm::Variable(name) => context.tys.iter().rev().enumerate().find_map(|(i, (name_1, ty))| {
			if &name == name_1 {
				Some((Term::Variable(Index(i)), ty.clone()))
			} else {
				None
			}
		}),
		RawTerm::Pair { .. } => None, // TODO: infer non-dependent pair?
		RawTerm::Lambda { .. } => None,
		RawTerm::Compute { scrutinee, eliminators: raw_eliminators } => {
			let (scrutinee, mut total_ty) = synthesize(context, *scrutinee)?;
			let mut eliminators = vec![];
			for raw_eliminator in raw_eliminators {
				match raw_eliminator {
					RawEliminator::Apply { argument } => {
						if let Value::Pi { parameter: _, base, family } = total_ty.as_ref() {
							let argument = verify(context, argument, base.clone())?;
							let argument_value = evaluate(context.environment.clone(), argument.clone());
							eliminators.push(Eliminator::Apply { argument });
							total_ty = family.clone().apply_value(argument_value);
						} else {
							return None;
						}
					}
					RawEliminator::ProjectBase => {
						if let Value::Sigma { parameter: _, base, family: _ } = total_ty.as_ref() {
							eliminators.push(Eliminator::ProjectBase);
							total_ty = base.clone();
						} else {
							return None;
						}
					}
					RawEliminator::ProjectFiber => {
						if let Value::Sigma { parameter: _, base: _, family } = total_ty.as_ref() {
							let basepoint_value = {
								let mut eliminators = eliminators.clone();
								eliminators.push(Eliminator::ProjectBase);
								evaluate(
									context.environment.clone(),
									Term::Compute { scrutinee: bx!(scrutinee.clone()), eliminators },
								)
							};
							eliminators.push(Eliminator::ProjectFiber);
							total_ty = family.clone().apply_value(basepoint_value);
						} else {
							return None;
						}
					}
				}
			}
			Some((Term::Compute { scrutinee: bx!(scrutinee), eliminators }, total_ty))
		}
		RawTerm::Universe => Some((Term::Universe, rc!(Value::Universe))),
		RawTerm::Pi { parameter, base, family } => {
			let base = verify(context, *base, rc!(Value::Universe))?;
			let base_value = evaluate(context.environment.clone(), base.clone());
			let family =
				verify(&context.clone().bind(parameter.clone(), base_value), *family, rc!(Value::Universe))?;
			Some((Term::Pi { parameter, base: bx!(base), family: bx!(family) }, rc!(Value::Universe)))
		}
		RawTerm::Sigma { parameter, base, family } => {
			let base = verify(context, *base, rc!(Value::Universe))?;
			let base_value = evaluate(context.environment.clone(), base.clone());
			let family =
				verify(&context.clone().bind(parameter.clone(), base_value), *family, rc!(Value::Universe))?;
			Some((Term::Sigma { parameter, base: bx!(base), family: bx!(family) }, rc!(Value::Universe)))
		}
		RawTerm::Let { assignee, ty: argument_ty, argument, tail } => {
			let argument_ty = verify(context, *argument_ty, rc!(Value::Universe))?;
			let argument_ty_value = evaluate(context.environment.clone(), argument_ty.clone());
			let argument = verify(context, *argument, argument_ty_value.clone())?;
			let argument_value = evaluate(context.environment.clone(), argument.clone());
			let (tail, tail_ty) =
				synthesize(&context.clone().extend(assignee.clone(), argument_ty_value, argument_value), *tail)?;
			Some((
				Term::Let { assignee, ty: bx!(argument_ty), argument: bx!(argument), tail: bx!(tail) },
				tail_ty,
			))
		}
	}
}

// Evaluation: Take an environment and a term, and produce a value.
// Precondition: Since term is a core term, it must be well-typed (and so must environment).
pub fn evaluate(environment: Environment, term: Term) -> Rc<Value> {
	use Term::*;
	match term {
		Variable(Index(index)) => environment[environment.len() - 1 - index].clone(),
		Lambda { parameter, body } =>
			rc!(Value::Lambda { parameter, body: Closure(environment.clone(), *body) }),
		Pair { basepoint, fiberpoint } => rc!(Value::Pair {
			basepoint: evaluate(environment.clone(), *basepoint),
			fiberpoint: evaluate(environment, *fiberpoint)
		}),
		Compute { scrutinee, eliminators } => {
			let mut scrutinee = evaluate(environment.clone(), *scrutinee);

			for eliminator in eliminators {
				match eliminator {
					Eliminator::Apply { argument } => {
						let argument = evaluate(environment.clone(), argument); // Note: an unnecessary clone is made here at the end of the loop.
						if let Value::Lambda { parameter: _, body } = scrutinee.as_ref() {
							scrutinee = body.clone().apply_value(argument)
						} else if let Value::Neutral { variable, eliminators } = scrutinee.as_ref() {
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::Apply { argument });
							scrutinee = rc!(Value::Neutral { variable: *variable, eliminators })
						} else {
							panic!();
						}
					}
					Eliminator::ProjectBase =>
						if let Value::Pair { basepoint, .. } = scrutinee.as_ref() {
							scrutinee = basepoint.clone();
						} else if let Value::Neutral { variable, eliminators } = scrutinee.as_ref() {
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::ProjectBase);
							scrutinee = rc!(Value::Neutral { variable: *variable, eliminators })
						} else {
							panic!();
						},
					Eliminator::ProjectFiber =>
						if let Value::Pair { fiberpoint, .. } = scrutinee.as_ref() {
							scrutinee = fiberpoint.clone();
						} else if let Value::Neutral { variable, eliminators } = scrutinee.as_ref() {
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::ProjectFiber);
							scrutinee = rc!(Value::Neutral { variable: *variable, eliminators })
						} else {
							panic!();
						},
				}
			}

			scrutinee
		}
		Universe => rc!(Value::Universe),
		Pi { parameter, base, family } => rc!(Value::Pi {
			parameter,
			base: evaluate(environment.clone(), *base),
			family: Closure(environment, *family),
		}),
		Sigma { parameter, base, family } => rc!(Value::Sigma {
			parameter,
			base: evaluate(environment.clone(), *base),
			family: Closure(environment, *family),
		}),
		Let { assignee: _, ty: _, argument, tail } => {
			let argument = evaluate(environment.clone(), *argument);
			let mut environment = environment.clone();
			environment.push(argument);
			evaluate(environment, *tail)
		}
	}
}

// Conversion checker (syntax-directed): Take the current level and determine if two values in this level are the same.
// (A type-directed conversion checker would take the type as well. This has the advantage of being able to conversion-check neutrals with neutrals, but this is deemed unnecessary. We have the option of putting neutral unit values into 'boxes' in the elaborator which can be conversion-checked with other 'boxes'.)
pub fn is_convertible(context_length: Level, left: Rc<Value>, right: Rc<Value>) -> bool {
	use Value::*;
	match (left.as_ref(), right.as_ref()) {
		(
			Neutral { variable: left_variable, eliminators: left_eliminators },
			Neutral { variable: right_variable, eliminators: right_eliminators },
		) =>
			left_variable == right_variable && {
				for eliminator_pair in left_eliminators.iter().zip(right_eliminators.iter()) {
					match eliminator_pair {
						(
							NeutralEliminator::Apply { argument: left_argument },
							NeutralEliminator::Apply { argument: right_argument },
						) =>
							if !is_convertible(context_length, left_argument.clone(), right_argument.clone()) {
								return false;
							},
						(NeutralEliminator::ProjectBase, NeutralEliminator::ProjectBase) => {}
						(NeutralEliminator::ProjectFiber, NeutralEliminator::ProjectFiber) => {}
						_ => return false,
					}
				}
				true
			},
		(Lambda { parameter: _, body: left_body }, Lambda { parameter: _, body: right_body }) =>
			is_convertible(
				context_length.suc(),
				left_body.clone().apply_value(rc!(Value::variable(context_length))),
				right_body.clone().apply_value(rc!(Value::variable(context_length))),
			),
		// Eta-conversion for functions.
		(Lambda { parameter: _, body: left_body }, Neutral { variable, eliminators }) => is_convertible(
			context_length.suc(),
			left_body.clone().apply_value(rc!(Value::variable(context_length))),
			rc!({
				let mut eliminators = eliminators.clone();
				eliminators.push(NeutralEliminator::Apply { argument: rc!(Value::variable(context_length)) });
				Neutral { variable: *variable, eliminators }
			}),
		),
		(Neutral { variable, eliminators }, Lambda { parameter: _, body: right_body }) => is_convertible(
			context_length.suc(),
			rc!({
				let mut eliminators = eliminators.clone();
				eliminators.push(NeutralEliminator::Apply { argument: rc!(Value::variable(context_length)) });
				Neutral { variable: *variable, eliminators }
			}),
			right_body.clone().apply_value(rc!(Value::variable(context_length))),
		),
		(
			Pair { basepoint: left_basepoint, fiberpoint: left_fiberpoint },
			Pair { basepoint: right_basepoint, fiberpoint: right_fiberpoint },
		) =>
			is_convertible(context_length, left_basepoint.clone(), right_basepoint.clone())
				&& is_convertible(context_length, left_fiberpoint.clone(), right_fiberpoint.clone()),
		// Eta-conversion for pairs.
		(
			Pair { basepoint: left_basepoint, fiberpoint: left_fiberpoint },
			Neutral { variable, eliminators },
		) => {
			let mut eliminators_basepoint = eliminators.clone();
			eliminators_basepoint.push(NeutralEliminator::ProjectBase);
			let mut eliminators_fiberpoint = eliminators.clone();
			eliminators_fiberpoint.push(NeutralEliminator::ProjectFiber);
			is_convertible(
				context_length,
				left_basepoint.clone(),
				rc!(Neutral { variable: *variable, eliminators: eliminators_basepoint }),
			) && is_convertible(
				context_length,
				left_fiberpoint.clone(),
				rc!(Neutral { variable: *variable, eliminators: eliminators_fiberpoint }),
			)
		}
		(
			Neutral { variable, eliminators },
			Pair { basepoint: right_basepoint, fiberpoint: right_fiberpoint },
		) => {
			let mut eliminators_basepoint = eliminators.clone();
			eliminators_basepoint.push(NeutralEliminator::ProjectBase);
			let mut eliminators_fiberpoint = eliminators.clone();
			eliminators_fiberpoint.push(NeutralEliminator::ProjectFiber);
			is_convertible(
				context_length,
				rc!(Neutral { variable: *variable, eliminators: eliminators_basepoint }),
				right_basepoint.clone(),
			) && is_convertible(
				context_length,
				rc!(Neutral { variable: *variable, eliminators: eliminators_fiberpoint }),
				right_fiberpoint.clone(),
			)
		}
		(
			Pi { parameter: _, base: left_base, family: left_family },
			Pi { parameter: _, base: right_base, family: right_family },
		) =>
			is_convertible(context_length, left_base.clone(), right_base.clone())
				&& is_convertible(
					context_length.suc(),
					left_family.clone().apply_value(rc!(Value::variable(context_length))),
					right_family.clone().apply_value(rc!(Value::variable(context_length))),
				),
		(
			Sigma { parameter: _, base: left_base, family: left_family },
			Sigma { parameter: _, base: right_base, family: right_family },
		) =>
			is_convertible(context_length, left_base.clone(), right_base.clone())
				&& is_convertible(
					context_length.suc(),
					left_family.clone().apply_value(rc!(Value::variable(context_length))),
					right_family.clone().apply_value(rc!(Value::variable(context_length))),
				),
		(Universe, Universe) => true,
		_ => false,
	}
}
