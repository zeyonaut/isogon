use std::{ffi::OsStr, fs};

use isogon::frontend::{elaborate::elaborate, lex::lex, parse::parse};

use crate::common::EXTENSION;

#[test]
fn run_fail_tests() {
	for path in fs::read_dir("tests/fail/programs")
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
