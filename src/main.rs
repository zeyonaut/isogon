#![feature(array_methods)]

use bpaf::{construct, short, Parser};
mod common;
mod ir;
mod op;

use op::{
	elaborate, evaluate::Evaluate, flatten::flatten, parse::parse, stage::Stage, unelaborate::Unelaborate,
	unevaluate::Unevaluate, unparse::pretty_print, unstage::Unstage,
};

use crate::op::linearize::linearize;

pub fn run(source: &str) {
	// Parsing.
	let (lexed_source, parsed_program, interner) = parse(source);
	let fragment = parsed_program.fragment;
	println!("Parsing complete.");

	println!();

	// Elaboration.
	let (term, ty) = elaborate(source, &lexed_source, parsed_program, &interner);
	println!("Elaboration complete.");
	println!("Elaborated term: {}", pretty_print(&term.clone().unelaborate(), &interner));
	println!("Synthesized type: {}", pretty_print(&ty.unevaluate().unelaborate(), &interner));
	println!("Evaluation: {}", pretty_print(&term.clone().evaluate().unevaluate().unelaborate(), &interner));

	println!();

	// Staging.
	let staged_term = term.stage();
	println!("Staging complete.");
	let unstaged_term = staged_term.unstage();
	println!("Staged term: {}", pretty_print(&unstaged_term.clone().unelaborate(), &interner));
	println!(
		"Evaluation: {}",
		pretty_print(&unstaged_term.clone().evaluate().unevaluate().unelaborate(), &interner)
	);

	// Early return for irrelevant programs.
	if fragment == 0 {
		return;
	}

	println!();

	// Closure conversion.
	let flat_term = flatten(&unstaged_term);
	println!("Closure conversion complete.");
	println!("Closure-converted program: {flat_term:?}");

	println!();

	// Linearization.
	let linearized_program = linearize(flat_term);
	println!("Linearization complete.");
	println!("Linearized program: {linearized_program:?}");
}

enum InputOption {
	Direct(String),
	FilePath(String),
}

struct Options {
	input: InputOption,
}

fn main() {
	let options: Options = construct!(Options {
		input(construct!([
			c(short('c').argument::<String>("\"preterm\"").help("Read input from argument").map(InputOption::Direct)),
			f(short('f').argument::<String>("PATH").help("Read input from file").map(InputOption::FilePath)),
		]))
	})
	.to_options()
	.run();

	let input = match options.input {
		InputOption::Direct(command) => command,
		InputOption::FilePath(file_path) => std::fs::read_to_string(file_path).unwrap(),
	};

	run(&input);
}
