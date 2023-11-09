// Non-staged; no unification.
mod alpha;
// Non-staged; with unification.
mod beta;
// Staged.
mod gamma;
mod utility;

mod parse;
use std::str::FromStr;

use bpaf::{construct, short, Parser};

enum LanguageOption {
	Alpha,
	Beta,
	Gamma,
}

impl FromStr for LanguageOption {
	type Err = String;

	fn from_str(s: &str) -> Result<Self, Self::Err> {
		use LanguageOption::*;
		match s {
			"a" => Ok(Alpha),
			"b" => Ok(Beta),
			"c" => Ok(Gamma),
			_ => Err("no such language".to_owned()),
		}
	}
}

enum InputOption {
	Direct(String),
	FilePath(String),
}

struct Options {
	language: LanguageOption,
	input: InputOption,
}

fn main() {
	let language = short('l').help("Choose language").argument::<LanguageOption>("{a, b, c}");
	let options: Options = construct!(Options {
		language,
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

	match options.language {
		LanguageOption::Alpha => alpha::run(&input),
		LanguageOption::Beta => beta::run(&input),
		LanguageOption::Gamma => gamma::run(&input),
	}
}
