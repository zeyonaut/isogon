use std::{ffi::OsStr, fs};

use isogon::{
	common::Fragment,
	ir::source::lex,
	op::{
		elaborate::elaborate,
		emit::emit_cranelift,
		evaluate::Evaluate,
		flatten::flatten,
		linearize::linearize,
		parse::parse,
		stage::{stage, Stage},
		unelaborate::Unelaborate,
		unevaluate::Unevaluate,
		unparse::pretty_print,
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
		let (term, _, kind) = elaborate(parsed_program).unwrap();
		let staged_term = stage(term.clone());
		let kind = kind.unevaluate().stage();

		if fragment == Fragment::Logical {
			return;
		}

		let program = flatten(&staged_term, kind);
		let linearized_program = linearize(program);
		let _emitted_program = emit_cranelift(&linearized_program);

		assert_eq!(
			pretty_print(&term.evaluate().unevaluate().unelaborate(), &resolver),
			pretty_print(&staged_term.clone().evaluate().unevaluate().unelaborate(), &resolver)
		);
	}
}
