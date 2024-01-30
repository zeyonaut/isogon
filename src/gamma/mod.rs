use lasso::Rodeo;

use self::{elaborator::DynamicTerm, lexer::LexError};
use crate::gamma::{
	closer::close,
	common::Level,
	elaborator::elaborate_dynamic_closed,
	evaluator::Evaluate,
	lexer::LexedSource,
	parser::Parser,
	sequentializer::sequentialize,
	sourcify::write_dynamic,
	stager::{Stage, Unstage},
};

mod closer;
mod common;
mod conversion;
mod elaborator;
mod evaluator;
mod lexer;
mod parser;
mod sequentializer;
mod sourcify;
mod stager;

pub fn run(source: &str) {
	let lexed_source = match LexedSource::new(source) {
		Ok(lexed_source) => lexed_source,
		Err(lex_error) => {
			print_lex_error(source, lex_error);
			return;
		}
	};
	let mut parser = Parser::new(source, lexed_source);
	let Some(term) = parser.parse_dynamic() else { panic!() };
	println!("parsed.");
	let (term, ty) = elaborate_dynamic_closed(term);

	println!("elaborated term: {}", pretty_print(&term, &parser.interner));
	println!("normalized type: {}", pretty_print(&ty.reify_closed(), &parser.interner));
	let value = term.stage(&stager::Environment::new());
	let term = value.clone().unstage(Level(0));
	println!("staged term: {}", pretty_print(&term, &parser.interner));

	let _closure_converted = close(value.clone());
	let _sequentialized = sequentialize(_closure_converted);

	let value = term.evaluate(&evaluator::Environment(Vec::new()));
	println!("evaluated: {}", pretty_print(&value.reify_closed(), &parser.interner));
}

fn pretty_print(term: &DynamicTerm, interner: &Rodeo) -> String {
	let mut s = String::new();
	write_dynamic(term, &mut s, interner).unwrap();
	s
}

pub fn print_lex_error(source: &str, LexError(location, kind): LexError) {
	const TAB_WIDTH: usize = 3;
	// SAFETY: Repeated spaces form a valid string.
	const TAB_REPLACEMENT: &'static str = unsafe { std::str::from_utf8_unchecked(&[b' '; TAB_WIDTH]) };

	let mut lines = source.split_inclusive('\n');
	let mut line_number: usize = 0;
	let mut bytes_left = location;
	let Some(line) = (loop {
		if let Some(line) = lines.next() {
			line_number += 1;
			if line.len() <= bytes_left {
				bytes_left -= line.len();
			} else {
				break Some(line);
			}
		} else {
			break None;
		}
	}) else {
		panic!("invalid lex error location");
	};

	fn char_list_string(chars: &[char]) -> String {
		if let Some(c) = chars.get(0) {
			use std::fmt::Write;
			let mut string = String::new();
			write!(string, "`{}`", c).unwrap();
			for c in chars.into_iter().skip(1) {
				write!(string, ", `{}`", c).unwrap();
			}
			string
		} else {
			String::new()
		}
	}

	let visual_line = line.replace('\t', &TAB_REPLACEMENT).trim_end().to_owned();
	let mut visual_offset: usize =
		unicode_width::UnicodeWidthStr::width(line[0..bytes_left].replace('\t', &TAB_REPLACEMENT).as_str());

	{
		use lexer::LexErrorKind::*;
		print!("[{}:{}] ", line_number, bytes_left);
		print!("error: ");
		match kind {
			UnrecognizedLexemePrefix =>
				println!("unrecognized lexeme prefix `{}`", &line[bytes_left..bytes_left + 1]),
			UnexpectedCharacter(expected) => println!(
				"expected one of {}; found `{}`",
				char_list_string(expected),
				&line[bytes_left..bytes_left + 1].escape_default()
			),
			UnexpectedEnd(expected) => {
				visual_offset += 1;
				println!("expected one of {}; found end of input", char_list_string(expected));
			}
		}
	}
	let displayed_line_number = line_number.to_string();
	let dummy_line_number = " ".repeat(displayed_line_number.len());
	println!("{} |", dummy_line_number);
	println!("{} | {}", displayed_line_number, visual_line);
	println!("{} | {}^", dummy_line_number, " ".repeat(visual_offset));
}
