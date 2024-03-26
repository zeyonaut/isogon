mod common;
mod ir;
mod sourcify;
mod transform;

use lasso::{Key, Rodeo};
use transform::{elaborate, evaluate::Evaluate, parse::parse};

use self::{ir::syntax::DynamicTerm, sourcify::write_dynamic};
use crate::delta::transform::unevaluate::Unevaluate;

pub fn run(source: &str) {
	// Parsing.
	let (lexed_source, preterm, interner) = parse(source);
	println!("Parsing complete.");

	println!();

	// Elaboration.
	let (term, ty) = elaborate(source, &lexed_source, preterm);
	println!("Elaboration complete.");
	println!("Elaborated term: {}", pretty_print(&term, &interner));
	println!("Synthesized type: {}", pretty_print(&ty.unevaluate(), &interner));
	println!("Evaluation: {}", pretty_print(&term.clone().evaluate().unevaluate(), &interner));

	println!();

	// Staging.
	// let staged_term = term.stage();
	// println!("Staging complete.");
	// let unstaged_term = staged_term.unstage();
	// println!("Staged term: {}", pretty_print(&unstaged_term, &interner));
	// println!("Evaluation: {}", pretty_print(&unstaged_term.clone().evaluate().unevaluate(), &interner));
}

fn pretty_print(term: &DynamicTerm, interner: &Rodeo) -> String {
	let mut s = String::new();
	write_dynamic(term, &mut s, interner).unwrap();
	s
}
