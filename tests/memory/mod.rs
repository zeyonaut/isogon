use std::{collections::HashMap, ffi::OsStr, fs};

use isogon::{
	backend::{
		flatten::flatten,
		interpret::{execute, Data},
		linearize::linearize,
		stage::stage,
	},
	common::{Fragment, Symbol},
	frontend::{
		elaborate::elaborate,
		evaluate::Evaluate as _,
		lex::lex,
		parse::parse,
		pretty::{unelaborate::Unelaborate as _, unparse::pretty_print},
		unevaluate::Unevaluate as _,
	},
};

use crate::common::EXTENSION;

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
			let (mut heap, data) = execute(&linearized_program);

			// Simulate a recursive deallocation of the return value.
			remove_reachable(&mut heap, &data);

			// Ensure that all dynamically allocated is either freed or transferred.
			assert!(heap.is_empty());
		}
	}
}

fn remove_reachable(heap: &mut HashMap<Symbol, Data>, data: &Data) {
	match data {
		Data::None | Data::PtrToNone | Data::Num(_) | Data::Enum(_, _) | Data::Procedure(_) => (),
		Data::Heap(s) => {
			let data = heap[s].clone();
			remove_reachable(heap, &data);
			heap.remove(s);
		}
		Data::Function { procedure: _, captures } => remove_reachable(heap, captures),
		Data::Captures(captures) =>
			for capture in captures.iter() {
				remove_reachable(heap, capture)
			},
		Data::Array(elements) =>
			for element in elements.iter() {
				remove_reachable(heap, element)
			},
		Data::Pair(a, b) => {
			remove_reachable(heap, a);
			remove_reachable(heap, b);
		}
	}
}
