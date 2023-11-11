use nom::{
	branch::alt,
	bytes::complete::tag,
	character::complete::{alpha1, alphanumeric1, multispace0},
	combinator::recognize,
	multi::many0,
	sequence::{delimited, pair, preceded, terminated},
	IResult,
};

use crate::utility::bx;

#[derive(Debug, Clone)]
pub enum StaticPreterm {
	Variable(String),
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Lift(Box<DynamicPreterm>),
	Quote(Box<DynamicPreterm>),
	Universe,
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
}

#[derive(Debug, Clone)]
pub enum DynamicPreterm {
	Variable(String),
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Splice(Box<StaticPreterm>),
	Universe,
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
}

pub fn parse_dynamic_eof(input: &str) -> IResult<&str, DynamicPreterm> {
	terminated(parse_dynamic, multispace0)(input)
}

fn parse_static(input: &str) -> IResult<&str, StaticPreterm> {
	alt((parse_static_let, parse_static_explicit_pi, parse_static_lambda, parse_static_atomic))(input)
}

fn parse_dynamic(input: &str) -> IResult<&str, DynamicPreterm> {
	alt((
		parse_dynamic_let::<true>,
		parse_dynamic_let::<false>,
		parse_dynamic_lambda,
		parse_dynamic_explicit_pi,
		parse_dynamic_atomic,
	))(input)
}

fn parse_static_lambda(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, parameter) = delimited(sym("|"), parse_identifier, sym("|"))(input)?;
	let (input, body) = parse_static(input)?;
	Ok((input, StaticPreterm::Lambda { parameter: parameter.to_string(), body: bx!(body) }))
}

fn parse_dynamic_lambda(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, parameter) = delimited(sym("|"), parse_identifier, sym("|"))(input)?;
	let (input, body) = parse_dynamic(input)?;
	Ok((input, DynamicPreterm::Lambda { parameter: parameter.to_string(), body: bx!(body) }))
}

fn parse_static_let(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, _) = sym("let")(input)?;
	let (input, assignee) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, ty) = parse_static(input)?;
	let (input, _) = sym("=")(input)?;
	let (input, argument) = parse_static(input)?;
	let (input, _) = sym(";")(input)?;
	let (input, tail) = parse_static(input)?;
	Ok((
		input,
		StaticPreterm::Let {
			assignee: assignee.to_string(),
			ty: bx!(ty),
			argument: bx!(argument),
			tail: bx!(tail),
		},
	))
}

fn parse_dynamic_let<const IS_DYNAMIC: bool>(input: &str) -> IResult<&str, DynamicPreterm> {
	if IS_DYNAMIC {
		let (input, _) = sym("let")(input)?;
		let (input, assignee) = parse_identifier(input)?;
		let (input, _) = sym(":")(input)?;
		let (input, ty) = parse_dynamic(input)?;
		let (input, _) = sym("=")(input)?;
		let (input, argument) = parse_dynamic(input)?;
		let (input, _) = sym(";")(input)?;
		let (input, tail) = parse_dynamic(input)?;
		Ok((
			input,
			DynamicPreterm::Let {
				assignee: assignee.to_string(),
				ty: bx!(ty),
				argument: bx!(argument),
				tail: bx!(tail),
			},
		))
	} else {
		let (input, _) = sym("def")(input)?;
		let (input, assignee) = parse_identifier(input)?;
		let (input, _) = sym(":")(input)?;
		let (input, ty) = parse_static(input)?;
		let (input, _) = sym("=")(input)?;
		let (input, argument) = parse_static(input)?;
		let (input, _) = sym(";")(input)?;
		let (input, tail) = parse_dynamic(input)?;
		Ok((
			input,
			DynamicPreterm::Splice(bx!(StaticPreterm::Let {
				assignee: assignee.to_string(),
				ty: bx!(ty),
				argument: bx!(argument),
				tail: bx!(StaticPreterm::Quote(bx!(tail))),
			})),
		))
	}
}

fn parse_static_explicit_pi(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, _) = sym("|")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_static(input)?;
	let (input, _) = sym("|")(input)?;
	let (input, _) = sym("->")(input)?;
	let (input, family) = parse_static(input)?;
	Ok((input, StaticPreterm::Pi { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}

fn parse_dynamic_explicit_pi(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, _) = sym("|")(input)?;
	let (input, parameter) = parse_identifier(input)?;
	let (input, _) = sym(":")(input)?;
	let (input, base) = parse_dynamic(input)?;
	let (input, _) = sym("|")(input)?;
	let (input, _) = sym("->")(input)?;
	let (input, family) = parse_dynamic(input)?;
	Ok((input, DynamicPreterm::Pi { parameter: parameter.to_string(), base: bx!(base), family: bx!(family) }))
}

fn parse_static_atomic(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, left) = parse_static_spine(input)?;
	if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("->")(input) {
		let (input, right) = parse_static(input)?;
		Ok((input, StaticPreterm::Pi { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else {
		Ok((input, left))
	}
}

fn parse_dynamic_atomic(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, left) = parse_dynamic_spine(input)?;
	if let Ok((input, _)) = sym::<_, _, nom::error::Error<_>>("->")(input) {
		let (input, right) = parse_dynamic(input)?;
		Ok((input, DynamicPreterm::Pi { parameter: "_".to_string(), base: bx!(left), family: bx!(right) }))
	} else {
		Ok((input, left))
	}
}

fn parse_static_spine(input: &str) -> IResult<&str, StaticPreterm> {
	let (mut input, mut atom) = parse_static_atom(input)?;
	while let Ok((next_input, argument)) = parse_static_atom(input) {
		input = next_input;
		atom = StaticPreterm::Apply { scrutinee: bx!(atom), argument: bx!(argument) }
	}
	Ok((input, atom))
}

fn parse_dynamic_spine(input: &str) -> IResult<&str, DynamicPreterm> {
	let (mut input, mut atom) = parse_dynamic_atom(input)?;
	while let Ok((next_input, argument)) = parse_dynamic_atom(input) {
		input = next_input;
		atom = DynamicPreterm::Apply { scrutinee: bx!(atom), argument: bx!(argument) }
	}
	Ok((input, atom))
}

fn parse_static_atom(input: &str) -> IResult<&str, StaticPreterm> {
	alt((
		parse_lift,
		parse_quote,
		parse_static_universe,
		parse_static_variable,
		delimited(sym("("), parse_static, sym("(")),
	))(input)
}

fn parse_dynamic_atom(input: &str) -> IResult<&str, DynamicPreterm> {
	alt((
		parse_splice,
		parse_dynamic_universe,
		parse_dynamic_variable,
		delimited(sym("("), parse_dynamic, sym(")")),
	))(input)
}

fn parse_lift(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, _) = sym("^")(input)?;
	let (input, liftee) = parse_dynamic_atom(input)?;
	Ok((input, StaticPreterm::Lift(bx!(liftee))))
}

fn parse_quote(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, _) = sym("[")(input)?;
	let (input, quotee) = parse_dynamic(input)?;
	let (input, _) = sym("]")(input)?;
	Ok((input, StaticPreterm::Quote(bx!(quotee))))
}

fn parse_splice(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, _) = sym("[")(input)?;
	let (input, splicee) = parse_static(input)?;
	let (input, _) = sym("]")(input)?;
	Ok((input, DynamicPreterm::Splice(bx!(splicee))))
}

fn parse_static_universe(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, _) = sym("*")(input)?;
	Ok((input, StaticPreterm::Universe))
}

fn parse_dynamic_universe(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, _) = sym("*")(input)?;
	Ok((input, DynamicPreterm::Universe))
}

fn parse_static_variable(input: &str) -> IResult<&str, StaticPreterm> {
	let (input, parsed) = parse_identifier(input)?;
	Ok((input, StaticPreterm::Variable(parsed.to_string())))
}

fn parse_dynamic_variable(input: &str) -> IResult<&str, DynamicPreterm> {
	let (input, parsed) = parse_identifier(input)?;
	Ok((input, DynamicPreterm::Variable(parsed.to_string())))
}

fn parse_identifier(input: &str) -> IResult<&str, &str> {
	preceded(multispace0, recognize(pair(alpha1, many0(alt((alphanumeric1, tag("_")))))))(input)
}

fn sym<T, Input, Error: nom::error::ParseError<Input>>(t: T) -> impl Fn(Input) -> IResult<Input, Input, Error>
where
	Input: nom::InputTake + nom::InputTakeAtPosition + nom::Compare<T>,
	T: nom::InputLength + Clone,
	<Input as nom::InputTakeAtPosition>::Item: nom::AsChar + Clone,
{
	move |input| preceded(multispace0, tag(t.clone()))(input)
}
