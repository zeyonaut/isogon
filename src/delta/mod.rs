mod common;
mod ir;
mod op;

use lasso::Rodeo;
use op::{elaborate, evaluate::Evaluate, parse::parse};

use self::ir::presyntax::PurePreterm;
use crate::delta::op::{
	stage::Stage, unelaborate::Unelaborate, unevaluate::Unevaluate, unparse::print, unstage::Unstage,
};

pub fn run(source: &str) {
	// Parsing.
	let (lexed_source, preterm, interner) = parse(source);
	println!("Parsing complete.");

	println!();

	// Elaboration.
	let (term, ty) = elaborate(source, &lexed_source, preterm);
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
}

fn pretty_print(term: &PurePreterm, interner: &Rodeo) -> String {
	let mut s = String::new();
	print(term, &mut s, interner).unwrap();
	s
}
