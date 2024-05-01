use std::{fs::File, io::Write, path::Path, str::FromStr};

use bpaf::{construct, long, short, Parser};
use isogon::{
	backend::{emit::emit_object, flatten::flatten, interpret::execute, linearize::linearize, stage::stage},
	common::Fragment,
	frontend::{
		elaborate::elaborate,
		evaluate::Evaluate as _,
		lex::lex,
		parse::parse,
		pretty::{
			report::{report_elaboration_error, report_parse_error, report_tokenization_error},
			unelaborate::Unelaborate as _,
			unparse::pretty_print,
		},
		unevaluate::Unevaluate as _,
	},
	ir::linear::pretty_print_linear,
};

fn main() {
	let options: Options = construct!(Options {
		input(construct!([
			c(short('c').argument::<String>("\"preterm\"").help("Read input from argument").map(InputOption::Direct)),
			f(short('f').argument::<String>("PATH").help("Read input from file").map(InputOption::FilePath)),
		])),
		show_lir(long("lir").switch()),
		show_clif(long("clif").switch()),
		object_path(short('o').argument::<String>("PATH").help("Emit object to file").optional()),
		target_triple(short('t').argument::<String>("target-triple").help("Code generation target").optional()),
	})
	.to_options()
	.run();

	run(options);
}

struct Options {
	input: InputOption,
	show_lir: bool,
	show_clif: bool,
	object_path: Option<String>,
	target_triple: Option<String>,
}

enum InputOption {
	Direct(String),
	FilePath(String),
}

fn run(options: Options) {
	let target_triple = options
		.target_triple
		.and_then(|triple| target_lexicon::Triple::from_str(&triple).ok())
		.unwrap_or_else(target_lexicon::Triple::host);
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
	let core_program = match elaborate(parsed_program) {
		Ok(x) => x,
		Err(e) => {
			report_elaboration_error(lexed_source, &resolver, e);
			panic!()
		}
	};
	println!("Elaboration complete.");
	println!("Elaborated term: {}", pretty_print(&core_program.term.clone().unelaborate(), &resolver));
	println!("Synthesized type: {}", pretty_print(&core_program.ty.unevaluate().unelaborate(), &resolver));
	if core_program.input.is_none() {
		println!(
			"Evaluation: {}",
			pretty_print(&core_program.term.clone().evaluate().unevaluate().unelaborate(), &resolver)
		);
	}

	println!();

	// Staging.
	let object_program = stage(core_program);
	println!("Staging complete.");
	println!("Staged term: {}", pretty_print(&object_program.term.clone().unelaborate(), &resolver));
	if object_program.input.is_none() {
		println!(
			"Evaluation: {}",
			pretty_print(&object_program.term.clone().evaluate().unevaluate().unelaborate(), &resolver)
		);
	}

	// Early return for irrelevant programs.
	if fragment == Fragment::Logical {
		return;
	}

	println!();

	// Closure conversion.
	let flat_program = flatten(&object_program);
	println!("Closure conversion complete.");

	println!();

	// Linearization.
	let linearized_program = linearize(flat_program);
	println!("Linearization complete.");

	if options.show_lir {
		let mut printed = String::new();
		println!();
		pretty_print_linear(&mut printed, &linearized_program).unwrap();
		print!("{printed}");
	}
	if linearized_program.entry_prototype.parameter.is_none() {
		let (heap, result) = execute(&linearized_program);
		println!("Execution heap: {heap:?}");
		println!("Execution result: {result:?}");
	}

	println!();

	// Emission
	let target_triple_string = target_triple.to_string();
	let emission = emit_object("program".to_owned(), &linearized_program, target_triple);
	println!("Emission to target {target_triple_string} complete.");

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
