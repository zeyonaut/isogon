use std::{
	ffi::OsStr,
	fs,
	path::{Path, PathBuf},
};

use isogon::{
	frontend::{elaborate::elaborate, lex::lex, parse::parse, pretty::report::report_elaboration_error},
	ir::syntax::CoreProgram,
};
use lasso::RodeoResolver;

pub const EXTENSION: &str = "is";

pub fn pass_frontend(path: PathBuf) -> (CoreProgram, RodeoResolver) {
	let path_str = path.as_os_str().to_str().unwrap().to_owned();
	let source = fs::read_to_string(path).expect(&path_str);
	let tokenized_source = lex(&source).ok().expect(&path_str);
	let (parsed_program, resolver) = parse(&tokenized_source).expect(&path_str);
	let core_program = match elaborate(parsed_program) {
		Ok(x) => x,
		Err(error) => {
			report_elaboration_error(tokenized_source, &resolver, error);
			panic!("{}", path_str);
		}
	};

	(core_program, resolver)
}

pub fn pass_frontend_directory(directory: impl AsRef<Path>) {
	for path in fs::read_dir(directory)
		.unwrap()
		.flatten()
		.map(|x| x.path())
		.filter(|x| x.extension() == Some(OsStr::new(EXTENSION)))
	{
		pass_frontend(path);
	}
}
