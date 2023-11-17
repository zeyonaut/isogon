use lasso::Rodeo;

use self::elaborator::DynamicTerm;
use crate::gamma::{
	common::Level,
	elaborator::elaborate_dynamic_closed,
	evaluator::Evaluate,
	parser::Parser,
	sourcify::write_dynamic,
	stager::{Stage, Unstage},
};

mod common;
mod conversion;
mod elaborator;
mod evaluator;
mod lexer;
mod parser;
mod sourcify;
mod stager;

fn pretty_print(term: &DynamicTerm, interner: &Rodeo) -> String {
	let mut s = String::new();
	write_dynamic(term, &mut s, interner).unwrap();
	s
}

pub fn run(source: &str) {
	let mut parser = Parser::new(source);
	let Some(term) = parser.parse_dynamic() else { panic!() };
	println!("parsed.");
	let (term, ty) = elaborate_dynamic_closed(term);

	println!("elaborated term: {}", pretty_print(&term, &parser.interner));
	println!("normalized type: {}", pretty_print(&ty.reify_closed(), &parser.interner));
	let value = term.stage(&stager::Environment::new());
	let term = value.unstage(Level(0));
	println!("staged term: {}", pretty_print(&term, &parser.interner));
	let value = term.evaluate(&evaluator::Environment(Vec::new()));
	println!("evaluated: {}", pretty_print(&value.reify_closed(), &parser.interner));
}
