use crate::gamma::{elaborator::elaborate_dynamic_closed, stager::stage};

mod common;
mod elaborator;
mod parser;
mod stager;

pub fn run(line: &str) {
	let ("", term) = parser::parse_dynamic_eof(&line).unwrap() else {
		panic!("parsing completed before end of input")
	};
	let (term, ty) = elaborate_dynamic_closed(term);
	println!("elaborated term: {}", term);
	println!("normalized type: {}", ty.reify());
	let value = stage(term);
	println!("staged term: {}", value.unstage());
}
