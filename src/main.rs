use bpaf::{construct, short, Parser};
use isogon::{
	common::Fragment,
	exec::linear::execute,
	ir::source::lex,
	op::{
		elaborate::elaborate, evaluate::Evaluate as _, flatten::flatten, linearize::linearize, parse::parse,
		stage::stage, unelaborate::Unelaborate as _, unevaluate::Unevaluate as _, unparse::pretty_print,
	},
	report::{report_elaboration_error, report_parse_error, report_tokenization_error},
};

pub fn run(source: &str) {
	// Parsing.
	let lexed_source = match lex(source) {
		Ok(x) => x,
		Err(e) => {
			report_tokenization_error(source, e);
			panic!()
		}
	};

	let (parsed_program, resolver) = match parse(&lexed_source) {
		Ok(x) => x,
		Err(e) => {
			report_parse_error(lexed_source, e);
			panic!()
		}
	};
	let fragment = parsed_program.fragment;
	println!("Parsing complete.");

	println!();

	// Elaboration.
	let (term, ty) = match elaborate(parsed_program) {
		Ok(x) => x,
		Err(e) => {
			report_elaboration_error(lexed_source, &resolver, e);
			panic!()
		}
	};
	println!("Elaboration complete.");
	println!("Elaborated term: {}", pretty_print(&term.clone().unelaborate(), &resolver));
	println!("Synthesized type: {}", pretty_print(&ty.unevaluate().unelaborate(), &resolver));
	println!("Evaluation: {}", pretty_print(&term.clone().evaluate().unevaluate().unelaborate(), &resolver));

	println!();

	// Staging.
	let staged_term = stage(term);
	println!("Staging complete.");
	println!("Staged term: {}", pretty_print(&staged_term.clone().unelaborate(), &resolver));
	println!(
		"Evaluation: {}",
		pretty_print(&staged_term.clone().evaluate().unevaluate().unelaborate(), &resolver)
	);

	// Early return for irrelevant programs.
	if fragment == Fragment::Logical {
		return;
	}

	println!();

	// Closure conversion.
	let flat_term = flatten(&staged_term);
	println!("Closure conversion complete.");

	println!();

	// Linearization.
	let linearized_program = linearize(flat_term);
	println!("Linearization complete.");
	let (heap, result) = execute(&linearized_program);
	println!("Execution heap: {heap:?}");
	println!("Execution result: {result:?}");
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
