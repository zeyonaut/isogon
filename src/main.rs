// Non-staged; no unification.
mod alpha;
// Non-staged; with unification.
mod beta;
// Staged.
mod gamma;
mod utility;

mod parse;
use parse::*;

fn main() {
	let mut line = String::new();
	std::io::stdin().read_line(&mut line).unwrap();

	beta::run(&line);
}
