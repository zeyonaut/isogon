mod alpha;
mod beta;
mod utility;

mod parse;
use parse::*;

fn main() {
	let mut line = String::new();
	std::io::stdin().read_line(&mut line).unwrap();

	beta::run(&line);
}
