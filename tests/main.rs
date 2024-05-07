mod common;
mod eta;

use std::{ffi::OsStr, fs};

use common::EXTENSION;
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
#[test]
fn run_fail_tests() {
	for path in fs::read_dir("tests/fail")
		.unwrap()
		.flatten()
		.map(|x| x.path())
		.filter(|x| x.extension() == Some(OsStr::new(EXTENSION)))
	{
		let path_str = path.as_os_str().to_str().unwrap().to_owned();
		let source = fs::read_to_string(path).expect(&path_str);
		let lexed_source = lex(&source).ok().expect(&path_str);
		let (preterm, _) = parse(&lexed_source).expect(&path_str);
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
		let path_str = path.as_os_str().to_str().unwrap().to_owned();
		let source = fs::read_to_string(path).expect(&path_str);
		let lexed_source = lex(&source).ok().expect(&path_str);
		let (parsed_program, resolver) = parse(&lexed_source).expect(&path_str);
		let fragment = parsed_program.fragment;
		let core_program = elaborate(parsed_program).expect(&path_str);
		let object_program = stage(core_program.clone());

		if object_program.input.is_none() {
			assert_eq!(
				pretty_print(&core_program.term.evaluate().unevaluate().unelaborate(), &resolver),
				pretty_print(&object_program.term.clone().evaluate().unevaluate().unelaborate(), &resolver)
			);
		}

		if fragment == Fragment::Logical {
			continue;
		}

		let flat_program = flatten(&object_program);
		let linearized_program = linearize(flat_program);
		if linearized_program.entry_prototype.parameter.is_none() {
			let _ = execute(&linearized_program);
		}
		let _emitted_object = emit_object(
			"program".to_owned(),
			&linearized_program,
			target_lexicon::triple!("x86_64-pc-windows-msvc"),
		);
	}
}
