mod common;
mod domain;
mod elaborator;
mod meta;
mod presyntax;
mod syntax;

use domain::evaluate;
use elaborator::{synthesize, Context};
use meta::Metacontext;
use presyntax::parse_term_eof;

pub fn run(line: &str) {
	let ("", term) = parse_term_eof(&line).unwrap() else {
		return;
	};
	println!("parsed.");
	let (term, ty) = synthesize(&mut Metacontext::new(), &Context::empty(), term).unwrap();
	println!("synthesized: {:?}", term);
	println!("synthesized type: {:?}", ty);
	let value = evaluate(Vec::new(), term);
	println!("evaluated: {:?}", value.as_ref());
}
