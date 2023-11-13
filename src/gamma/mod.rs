use lasso::Rodeo;

use self::elaborator::DynamicTerm;
use crate::gamma::{
	elaborator::{elaborate_dynamic_closed, write_dynamic},
	parser::Parser,
	stager::stage,
};

mod common;
mod elaborator;
mod lexer;
mod parser;
mod stager;

fn pretty_print(term: &DynamicTerm, interner: &Rodeo) -> String {
	let mut s = String::new();
	write_dynamic(term, &mut s, interner).unwrap();
	s
}

pub fn run(source: &str) {
	let mut parser = Parser::new(source);
	let Some(term) = parser.parse_dynamic() else { panic!() };
	let (term, ty) = elaborate_dynamic_closed(term);

	println!("elaborated term: {}", pretty_print(&term, &parser.interner));
	println!("normalized type: {}", pretty_print(&ty.reify(), &parser.interner));
	let value = stage(term);
	println!("staged term: {}", pretty_print(&value.unstage(), &parser.interner));
}
