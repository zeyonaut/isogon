mod common;
mod elaborator;
mod parser;
mod stager;

pub fn run(line: &str) {
	let ("", term) = parser::parse_dynamic_eof(&line).unwrap() else {
		panic!("parsing completed before end of input")
	};
	println!("parsed: {:?}", term);
}
