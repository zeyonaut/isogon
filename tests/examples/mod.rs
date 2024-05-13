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
	ir::semantics,
};

use crate::common::EXTENSION;

/// Ensures all examples are accepted by the elaborator, staged correctly, and compiled without error.
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

		let environment = semantics::Environment(if let Some(t) = &object_program.input {
			vec![semantics::Value::Dynamic(semantics::DynamicValue::Neutral(
				semantics::DynamicNeutral::Variable(t.0, isogon::common::Level(0)),
			))]
		} else {
			vec![]
		});

		let mut restaged_program = core_program.clone();
		restaged_program.term = object_program.term.clone();
		let restaged_program = stage(restaged_program);

		let evaluation_0 = pretty_print(
			&core_program.term.evaluate_in(&environment).unevaluate_in(environment.level()).unelaborate(),
			&resolver,
		);
		let evaluation_1 = pretty_print(
			&object_program
				.term
				.clone()
				.evaluate_in(&environment)
				.unevaluate_in(environment.level())
				.unelaborate(),
			&resolver,
		);
		let evaluation_2 = pretty_print(
			&restaged_program.term.evaluate_in(&environment).unevaluate_in(environment.level()).unelaborate(),
			&resolver,
		);

		assert_eq!(evaluation_0, evaluation_1);
		assert_eq!(evaluation_1, evaluation_2);

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
