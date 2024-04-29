use std::{fs::File, io::Write, path::Path};

use bpaf::{construct, long, short, Parser};
use isogon::{
	common::Fragment,
	exec::linear::execute,
	ir::{linear::pretty_print_linear, source::lex},
	op::{
		elaborate::elaborate,
		emit::emit_object,
		evaluate::Evaluate as _,
		flatten::flatten,
		linearize::linearize,
		parse::parse,
		stage::{stage, Stage},
		unelaborate::Unelaborate as _,
		unevaluate::Unevaluate as _,
		unparse::pretty_print,
	},
	report::{report_elaboration_error, report_parse_error, report_tokenization_error},
};

fn run(options: Options) {
	let source = match options.input {
		InputOption::Direct(command) => command,
		InputOption::FilePath(file_path) => std::fs::read_to_string(file_path).unwrap(),
	};

	// Parsing.
	let lexed_source = match lex(&source) {
		Ok(x) => x,
		Err(e) => {
			report_tokenization_error(&source, e);
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
	let (term, ty, kind) = match elaborate(parsed_program) {
		Ok(x) => x,
		Err(e) => {
			report_elaboration_error(lexed_source, &resolver, e);
			panic!()
		}
	};
	let kind = kind.unevaluate().stage();
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
	let flat_term = flatten(&staged_term, kind);
	println!("Closure conversion complete.");

	println!();

	// Linearization.
	let linearized_program = linearize(flat_term);
	println!("Linearization complete.");

	if options.show_lir {
		let mut printed = String::new();
		println!();
		pretty_print_linear(&mut printed, &linearized_program).unwrap();
		print!("{printed}");
	}
	let (heap, result) = execute(&linearized_program);
	println!("Execution heap: {heap:?}");
	println!("Execution result: {result:?}");

	println!();

	// Emission
	let emission = emit_object("program".to_owned(), &linearized_program);
	println!("Emission complete.");

	if options.show_clif {
		println!();
		println!("{}", emission.entry.display());
		for function in &emission.functions {
			println!("{}", function.display());
		}
	}

	// Object file generation.
	if let Some(object_path) = options.object_path {
		let object_path = Path::new(&object_path);
		// Create parent directories and file.
		std::fs::create_dir_all(object_path.parent().unwrap()).unwrap();
		let mut object_file = File::create(object_path).expect("failed to create object file");
		let object_buffer = emission.object.write().unwrap();
		object_file.write_all(&object_buffer).unwrap();
	}
}

enum InputOption {
	Direct(String),
	FilePath(String),
}

struct Options {
	input: InputOption,
	show_lir: bool,
	show_clif: bool,
	object_path: Option<String>,
}

fn main() {
	let options: Options = construct!(Options {
		input(construct!([
			c(short('c').argument::<String>("\"preterm\"").help("Read input from argument").map(InputOption::Direct)),
			f(short('f').argument::<String>("PATH").help("Read input from file").map(InputOption::FilePath)),
		])),
		show_lir(long("lir").switch()),
		show_clif(long("clif").switch()),
		object_path(short('o').argument::<String>("PATH").help("Emit object to file").optional())
	})
	.to_options()
	.run();

	run(options);
}
