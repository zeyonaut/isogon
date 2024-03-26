use lasso::Rodeo;

use crate::delta::{
	common::{any_bind, bind, AnyBinder, Copyability, Name, ReprAtom},
	ir::{
		presyntax::{Constructor, Expression, Former, Preterm},
		source::{Keyword, LexError, LexErrorKind, LexedSource, Token},
	},
};

/// Parses a dynamic preterm from a source string.
pub fn parse(source: &str) -> (LexedSource, Expression, Rodeo) {
	let lexed_source = match LexedSource::new(source) {
		Ok(lexed_source) => lexed_source,
		Err(lex_error) => {
			report_line_error(source, (lex_error.0, lex_error.0 + 1), &format_lex_error(source, lex_error));
			panic!();
		}
	};
	let mut parser = Parser {
		source,
		interner: Rodeo::new(),
		// TODO: Remove this clone.
		ranges: lexed_source.ranges.clone(),
	};
	let preterm = match presyntax_parse::program(&lexed_source.tokens, &mut parser) {
		Ok(preterm) => preterm,
		Err(error) => {
			report_line_error(
				source,
				lexed_source.ranges.get(error.location).copied().unwrap_or((source.len(), source.len() + 1)),
				&format!("parse error: expected one of: {:?}", error.expected.tokens().collect::<Vec<_>>()),
			);
			panic!();
		}
	};

	(lexed_source, preterm, parser.interner)
}
pub fn format_lex_error(source: &str, LexError(location, kind): LexError) -> String {
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
	}
}

pub fn report_line_error(source: &str, range: (usize, usize), error_string: &str) {
	const TAB_WIDTH: usize = 3;
	// SAFETY: Repeated spaces form a valid string.
	const TAB_REPLACEMENT: &'static str = unsafe { std::str::from_utf8_unchecked(&[b' '; TAB_WIDTH]) };

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

	let visual_line = line.replace('\t', &TAB_REPLACEMENT).trim_end().to_owned();
	let visual_offset: usize =
		unicode_width::UnicodeWidthStr::width(line[0..bytes_left].replace('\t', &TAB_REPLACEMENT).as_str());

	let displayed_line_number = line_number.to_string();
	let dummy_line_number = " ".repeat(displayed_line_number.len());
	println!("{} |", dummy_line_number);
	println!("{} | {}", displayed_line_number, visual_line);
	println!("{} | {}{}", dummy_line_number, " ".repeat(visual_offset), "^".repeat(width));
}

pub struct Parser<'s> {
	source: &'s str,
	pub interner: Rodeo,
	ranges: Box<[(usize, usize)]>,
}

impl<'s> Parser<'s> {
	fn identifier(&mut self, token_index: usize) -> Name {
		let range = self.ranges[token_index];
		let span = &self.source[range.0..range.1];
		self.interner.get_or_intern(span)
	}

	fn number(&self, token_index: usize) -> Option<usize> {
		let range = self.ranges[token_index];
		let span = &self.source[range.0..range.1];
		span.parse::<usize>().ok()
	}
}

peg::parser! {
  grammar presyntax_parse(parser: &mut Parser) for [Token] {
		rule _ = [Token::Whitespace]*

		rule identifier() -> Name
			= pos:position!() [Token::Identifier] {parser.identifier(pos)}

		rule number() -> usize
			= pos:position!() [Token::Number] {parser.number(pos).unwrap()}

		rule optional_parameter() -> Option<Name>
			= name:identifier() {Some(name)} / [Token::LowDash] {None}

		rule grade() -> Option<usize>
			= number:number() {Some(number)} / [Token::LowDash] {None}

		rule former() -> Former
			= [Token::Tick] {Former::Lift}
			/ [Token::Keyword(Keyword::Copy)] {Former::Copy}
			/ [Token::Keyword(Keyword::Repr)] {Former::Repr}
			/ [Token::Ast] {Former::Universe}

		rule constructor() -> Constructor
			= [Token::Keyword(Keyword::C0)] {Constructor::Copyability(Copyability::Trivial)}
			/ [Token::Keyword(Keyword::C1)] {Constructor::Copyability(Copyability::Nontrivial)}
			/ [Token::Keyword(Keyword::CMax)] {Constructor::CopyMax}
			/ [Token::Keyword(Keyword::RClass)] {Constructor::ReprAtom(Some(ReprAtom::Class))}
			/ [Token::Keyword(Keyword::RPointer)] {Constructor::ReprAtom(Some(ReprAtom::Pointer))}
			/ [Token::Keyword(Keyword::RByte)] {Constructor::ReprAtom(Some(ReprAtom::Byte))}
			/ [Token::Keyword(Keyword::RNat)] {Constructor::ReprAtom(Some(ReprAtom::Nat))}
			/ [Token::Keyword(Keyword::RFun)] {Constructor::ReprAtom(Some(ReprAtom::Fun))}
			/ [Token::Keyword(Keyword::RNone)] {Constructor::ReprAtom(None)}
			/ [Token::Keyword(Keyword::RPair)] {Constructor::ReprPair}
			/ [Token::Keyword(Keyword::RMax)] {Constructor::ReprMax}
			/ [Token::Keyword(Keyword::RUniv)] {Constructor::ReprUniv}

		rule atom() -> Expression
			= [Token::ParenL] _ preterm:preterm() _ [Token::ParenR] {preterm}
			/ init:position!() preterm:(
				  [Token::SquareL] _ preterm:preterm() _ [Token::SquareR] {Preterm::Splice(preterm.into())}
				/ [Token::AngleL] _ preterm:preterm() _ [Token::AngleR] {Preterm::Quote(preterm.into())}
				/ identifier:identifier() {Preterm::Variable(identifier)}
				/ former:former() {Preterm::Former(former, vec![])}
				/ constructor:constructor() {Preterm::Constructor(constructor, vec![])}
			) fini:position!() {preterm.at((init, fini))}

		rule bound_spine_headed() -> AnyBinder<Box<Expression>>
			= [Token::Pipe] _ variables:(variable:optional_parameter())**[Token::Period] _ [Token::Pipe] _ body:spine_headed() {any_bind(variables, body)}

		// Spines: projections, calls, and case-splits.
		#[cache_left_rec]
		rule spine() -> Expression
			= init:position!() preterm:(
				  former:former() arguments:(_ a:atom() {a})* {Preterm::Former(former, arguments)}
				/ constructor:constructor() arguments:(_ a:atom() {a})* {Preterm::Constructor(constructor, arguments)}
				/ callee:spine() _ argument:atom()
					{ Preterm::Call { callee: callee.into(), argument: argument.into() } }
			) fini:position!() {preterm.at((init, fini))}
			/ atom()

		#[cache]
		rule spine_headed() -> Expression
			// TODO: Refactor to avoid caching?
			= init:position!() preterm:(
				  [Token::Pipe] _ parameter:optional_parameter() _ [Token::At] _ grade:grade() _ [Token::Pipe] _ body:spine_headed() {Preterm::Lambda { grade, body: bind([parameter], body) }}
				/ [Token::Pipe] _ parameter:optional_parameter() _ [Token::At] _ grade:grade() _ [Token::Colon] _ base:spine_headed() _ [Token::Pipe] _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { grade, base: base.into(), family: bind([parameter], right) }}
				/ left:spine() _ [Token::At] _ grade:grade() _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { grade, base: left.into(), family: bind([None], right) }}
			) fini:position!() {preterm.at((init, fini))}
			/ spine()

		rule preterm() -> Expression
			= init:position!() preterm:(
				  [Token::Keyword(Keyword::Let)] _ name:optional_parameter() _ [Token::At] _ grade:grade() _ [Token::Colon] _ ty:spine_headed() _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm()
				{ Preterm::Let { grade, ty: ty.into(), argument: argument.into(), tail: bind([name], tail) }}
			) fini:position!() {preterm.at((init, fini))}
			/ init:position!() [Token::Keyword(Keyword::Def)] _ name:optional_parameter() _ [Token::At] _ grade:grade() _ [Token::Colon] _ ty:spine_headed() _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm() fini:position!()
			{
				let tail_range = tail.range;
				Preterm::Splice(Preterm::Let { grade, ty: ty.into(), argument: argument.into(), tail: bind([name], Preterm::Quote(tail.into()).at((tail_range.0, tail_range.1))) }.at((init, fini)).into()).at((init, fini))
			}
			/ spine_headed()

		pub rule program() -> Expression
			= _ preterm:preterm() _ {preterm}

  }
}
