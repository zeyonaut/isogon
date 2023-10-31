use nom::{
	branch::alt,
	bytes::complete::tag,
	character::complete::{alpha1, alphanumeric1, multispace0},
	combinator::recognize,
	multi::many0,
	sequence::{delimited, pair, preceded, terminated},
	IResult,
};

use super::common::Name;
use crate::{parse::fold_many0_once, utility::bx};

#[derive(Debug)]
pub enum RawEliminator {
	Apply { argument: Preterm },
	ProjectBase,
	ProjectFiber,
}

// The raw syntax: the output of the parser and the input of the elaborator.
#[derive(Debug)]
pub enum Preterm {
	Variable(Name),
	Lambda { parameter: Name, body: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Compute { scrutinee: Box<Self>, eliminators: Vec<RawEliminator> }, // This should have a positive number of eliminators.
	Universe, // We'll use type-in-type for convenience of implementation.
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Hole,
}

pub fn parse_term_eof(input: &str) -> IResult<&str, Preterm> {
	terminated(parse_term, multispace0)(input)
}

fn parse_term(input: &str) -> IResult<&str, Preterm> {
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

fn parse_universe(input: &str) -> IResult<&str, Preterm> {
	let (input, _) = sym("@type")(input)?;
	Ok((input, Preterm::Universe))
}

fn parse_hole(input: &str) -> IResult<&str, Preterm> {
	let (input, _) = sym("_")(input)?;
	Ok((input, Preterm::Hole))
}

fn parse_variable(input: &str) -> IResult<&str, Preterm> {
	let (input, parsed) = parse_identifier(input)?;
	Ok((input, Preterm::Variable(parsed.to_string())))
}

fn parse_atom(input: &str) -> IResult<&str, Preterm> {
	alt((parse_hole, parse_universe, parse_variable, delimited(sym("{"), parse_term, sym("}"))))(input)
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

fn parse_spine(input: &str) -> IResult<&str, Preterm> {
	let (input, atom) = parse_atom(input)?;
	let mut eliminators = vec![];
	let (input, ()) =
		fold_many0_once(parse_vertebra, move || (), |(), eliminator| eliminators.push(eliminator))(input)?;
	Ok((
		input,
		if eliminators.is_empty() { atom } else { Preterm::Compute { scrutinee: bx!(atom), eliminators } },
	))
}

fn parse_spine_or_implicit_sigma_or_implicit_pi_or_pair(input: &str) -> IResult<&str, Preterm> {
	let (input, left) = parse_spine(input)?;
	if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("*")(input) {
		let (input, right) = parse_term(input)?;
		Ok((input, Preterm::Sigma { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("->")(input) {
		let (input, right) = parse_term(input)?;
		Ok((input, Preterm::Pi { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>(",")(input) {
		let (input, right) = parse_spine_or_implicit_sigma_or_implicit_pi_or_pair(input)?;
		Ok((input, Preterm::Pair { basepoint: bx!(left), fiberpoint: bx!(right) }))
	} else {
		Ok((input, left))
	}
}

fn parse_lambda(input: &str) -> IResult<&str, Preterm> {
	let (input, parameter) = delimited(sym("("), parse_identifier, sym(")"))(input)?;
	let (input, _) = sym("=>")(input)?;
	let (input, body) = parse_term(input)?;
	Ok((input, Preterm::Lambda { parameter: parameter.to_string(), body: bx!(body) }))
}

fn parse_let(input: &str) -> IResult<&str, Preterm> {
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
		Preterm::Let { assignee: assignee.to_string(), ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) },
	))
}

fn parse_explicit_pi(input: &str) -> IResult<&str, Preterm> {
	let (input, _) = sym("(")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_term(input)?;
	let (input, _) = sym(")")(input)?;
	let (input, _) = sym("->")(input)?;
	let (input, family) = parse_term(input)?;
	Ok((input, Preterm::Pi { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}

fn parse_explicit_sigma(input: &str) -> IResult<&str, Preterm> {
	let (input, _) = sym("(")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_term(input)?;
	let (input, _) = sym(")")(input)?;
	let (input, _) = sym("*")(input)?;
	let (input, family) = parse_term(input)?;
	Ok((input, Preterm::Sigma { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}
/*
	Expr: {...}
	Variables: a-zA-Z_[a-zA-Z0-9_]*
	Lambda: (Variable) => V...
	Universe: @type
	Pi: (Variable: Expr) -> Expr
	Let: @let x = 2; ...
	Hole: _
*/
