mod common;
mod ir;
mod sourcify;
mod transform;

use lasso::{Key, Rodeo};
use transform::{
	close, elaborate, evaluate::Evaluate, linearize, parse::parse, stage::Stage, unstage::Unstage,
};

use self::{ir::syntax::DynamicTerm, sourcify::write_dynamic};
use crate::gamma::transform::unevaluate::Unevaluate;

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
	let staged_term = term.stage();
	println!("Staging complete.");
	let unstaged_term = staged_term.unstage();
	println!("Staged term: {}", pretty_print(&unstaged_term, &interner));
	println!("Evaluation: {}", pretty_print(&unstaged_term.clone().evaluate().unevaluate(), &interner));

	println!();

	// Closure conversion.
	let flat_program = close(unstaged_term);
	println!("Closure conversion complete.");

	println!();

	// Linearization.
	let linear_program = linearize(flat_program);
	println!("Linearization complete.");
	println!("Linearized program:");
	linear_program.pretty(&interner);

	// TODO: Lower to Cranelift.
}

fn pretty_print(term: &DynamicTerm, interner: &Rodeo) -> String {
	let mut s = String::new();
	write_dynamic(term, &mut s, interner).unwrap();
	s
}
