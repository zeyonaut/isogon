use std::{ffi::OsStr, fs};

use isogon::{
	backend::{emit::emit_object, flatten::flatten, interpret::execute, linearize::linearize, stage::stage},
	common::Fragment,
	frontend::{
		elaborate::elaborate,
		evaluate::Evaluate as _,
		lex::lex,
		parse::parse,
		pretty::{unelaborate::Unelaborate as _, unparse::pretty_print},
		unevaluate::Unevaluate as _,
	},
};

const EXTENSION: &str = "is";

#[test]
fn run_fail_tests() {
	for path in fs::read_dir("tests/fail")
		.unwrap()
		.flatten()
		.map(|x| x.path())
		.filter(|x| x.extension() == Some(OsStr::new(EXTENSION)))
	{
		let source = fs::read_to_string(path).unwrap();
		let lexed_source = lex(&source).ok().unwrap();
		let (preterm, _) = parse(&lexed_source).ok().unwrap();
		let term = elaborate(preterm);
		assert!(term.is_err());
	}
}

#[test]
fn run_examples() {
	for path in fs::read_dir("examples")
		.unwrap()
		.flatten()
		.map(|x| x.path())
		.filter(|x| x.extension() == Some(OsStr::new(EXTENSION)))
	{
		let source = fs::read_to_string(path).unwrap();
		let lexed_source = lex(&source).ok().unwrap();
		let (parsed_program, resolver) = parse(&lexed_source).ok().unwrap();
		let fragment = parsed_program.fragment;
		let core_program = elaborate(parsed_program).unwrap();
		let object_program = stage(core_program.clone());

		assert_eq!(
			pretty_print(&core_program.term.evaluate().unevaluate().unelaborate(), &resolver),
			pretty_print(&object_program.term.clone().evaluate().unevaluate().unelaborate(), &resolver)
		);

		if fragment == Fragment::Logical {
			return;
		}

		let flat_program = flatten(&object_program);
		let linearized_program = linearize(flat_program);
		let _ = execute(&linearized_program);
		let _emitted_object = emit_object(
			"program".to_owned(),
			&linearized_program,
			target_lexicon::triple!("x86_64-pc-windows-msvc"),
		);
	}
}
