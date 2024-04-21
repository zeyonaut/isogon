use lasso::Resolver;
use peg::error::ParseError;

use crate::{
	ir::source::{LexError, LexErrorKind, LexedSource},
	op::{
		elaborate::{ElaborationError, ElaborationErrorKind},
		unelaborate::Unelaborate as _,
		unparse::print,
	},
};

pub fn report_tokenization_error(source: &str, lex_error: LexError) {
	report_line_error(source, (lex_error.0, lex_error.0 + 1), &format_lex_error(source, lex_error))
}

pub fn report_parse_error(source: LexedSource, error: ParseError<usize>) {
	report_line_error(
		source.source,
		source.ranges.get(error.location).copied().unwrap_or((source.source.len(), source.source.len() + 1)),
		&format!("parse error: expected one of: {:?}", error.expected.tokens().collect::<Vec<_>>()),
	);
}

pub fn report_elaboration_error(source: LexedSource, interner: &impl Resolver, error: ElaborationError) {
	report_line_error(
		source.source,
		source.ranges.get(error.range.0).copied().unwrap_or((source.source.len(), source.source.len() + 1)),
		&display_error(error.kind, interner),
	);
}

fn report_line_error(source: &str, range: (usize, usize), error_string: &str) {
	const TAB_WIDTH: usize = 3;
	// SAFETY: Repeated spaces form a valid string.
	const TAB_REPLACEMENT: &str = unsafe { std::str::from_utf8_unchecked(&[b' '; TAB_WIDTH]) };

	let mut lines = source.split_inclusive('\n');
	let mut line_number: usize = 0;
	let mut bytes_left = range.0;
	let (line, bytes_left, width) = loop {
		if let Some(line) = lines.next() {
			line_number += 1;
			if line.len() <= bytes_left {
				bytes_left -= line.len();
			} else {
				break (line, bytes_left, range.1 - range.0);
			}
		} else {
			// This is a cold path, so this is fine.
			let (i, last) = source.split('\n').enumerate().last().unwrap();
			line_number = i + 1;
			break (last, last.len(), 1);
		}
	};

	print!("[{}:{}] ", line_number, bytes_left);
	println!("error: {error_string}");

	let visual_line = line.replace('\t', TAB_REPLACEMENT).trim_end().to_owned();
	let visual_offset: usize =
		unicode_width::UnicodeWidthStr::width(line[0..bytes_left].replace('\t', TAB_REPLACEMENT).as_str());

	let displayed_line_number = line_number.to_string();
	let dummy_line_number = " ".repeat(displayed_line_number.len());
	println!("{} |", dummy_line_number);
	println!("{} | {}", displayed_line_number, visual_line);
	println!("{} | {}{}", dummy_line_number, " ".repeat(visual_offset), "^".repeat(width));
}

fn format_lex_error(source: &str, LexError(location, kind): LexError) -> String {
	fn char_list_string(chars: &[char]) -> String {
		if let Some(c) = chars.first() {
			use std::fmt::Write;
			let mut string = String::new();
			write!(string, "`{}`", c).unwrap();
			for c in chars.iter().skip(1) {
				write!(string, ", `{}`", c).unwrap();
			}
			string
		} else {
			String::new()
		}
	}

	match kind {
		LexErrorKind::UnrecognizedLexemePrefix =>
			format!("lex error: unrecognized lexeme prefix `{}`", &source[location..location + 1]),
		LexErrorKind::UnexpectedCharacter(expected) => format!(
			"lex error: expected one of {}; found `{}`",
			char_list_string(expected),
			&source[location..location + 1].escape_default()
		),
		LexErrorKind::UnexpectedEnd(expected) => {
			format!("lex error: expected one of {}; found end of input", char_list_string(expected))
		}
		LexErrorKind::InvalidPragma => "invalid pragma".to_owned(),
	}
}

fn display_error(kind: ElaborationErrorKind, interner: &impl Resolver) -> String {
	match kind {
		ElaborationErrorKind::StaticBidirectionalMismatch { synthesized, expected } => {
			println!("elaboration error: type mismatch\nexpected: {synthesized:#?}\nfound: {expected:#?}");
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner).unwrap();
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner).unwrap();
			format!("elaboration error: type mismatch\nexpected: {}\nfound: {}", ty_ex, ty_sy)
		}
		ElaborationErrorKind::DynamicBidirectionalMismatch { synthesized, expected } => {
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner).unwrap();
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner).unwrap();
			format!("elaboration error: type mismatch\nexpected: {}\nfound: {}", ty_ex, ty_sy)
		}
		_ => format!("elaboration error: {:#?}", kind),
	}
}
