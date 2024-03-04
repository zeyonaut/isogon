use lasso::Rodeo;

use crate::gamma::{
	common::{Copyability, Name, ReprAtom},
	ir::{
		presyntax::{Constructor, Former, Pattern, Preterm, Projector},
		source::{Keyword, LexError, LexErrorKind, LexedSource, Token},
	},
};

/// Parses a dynamic preterm from a source string.
pub fn parse(source: &str) -> (Preterm, Rodeo) {
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
				&format!("parse error: expected one of: {:?}", error.expected),
			);
			panic!();
		}
	};

	(preterm, parser.interner)
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

fn report_line_error(source: &str, range: (usize, usize), error_string: &str) {
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
			let last = source.split_inclusive('\n').last().unwrap();
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
			= _ pos:position!() [Token::Identifier] {parser.identifier(pos)}

		rule number() -> usize
			= _ pos:position!() [Token::Number] {parser.number(pos).unwrap()}

		rule former() -> Former
			= _ a:([Token::Tick] {Former::Lift}
			/ [Token::Keyword(Keyword::RcType)] {Former::Rc}
			/ [Token::Keyword(Keyword::WrapType)] {Former::Wrap}
			/ [Token::Keyword(Keyword::Nat)] {Former::Nat}
			/ [Token::Keyword(Keyword::Bool)] {Former::Bool}
			/ [Token::Keyword(Keyword::Copy)] {Former::Copy}
			/ [Token::Keyword(Keyword::Repr)] {Former::Repr}
			/ [Token::Ast] {Former::Universe}) {a}

		rule constructor() -> Constructor
			= _ a:([Token::Keyword(Keyword::RcNew)] {Constructor::Rc}
			/ [Token::Keyword(Keyword::WrapNew)] {Constructor::Wrap}
			/ number:number() {Constructor::Num(number)}
			/ [Token::Keyword(Keyword::Suc)] {Constructor::Suc}
			/ [Token::Keyword(Keyword::False)] {Constructor::BoolValue(false)}
			/ [Token::Keyword(Keyword::True)] {Constructor::BoolValue(true)}
			/ [Token::Keyword(Keyword::C0)] {Constructor::Copyability(Copyability::Trivial)}
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
			/ [Token::Keyword(Keyword::RUniv)] {Constructor::ReprUniv}) {a}

		rule projector() -> Projector
			= _ a:([Token::Keyword(Keyword::UnRc)] {Projector::Rc}
			/ [Token::Keyword(Keyword::Unwrap)] {Projector::Wrap}
			/ [Token::Project(projection)] {Projector::Field(projection)}) {a}

		rule atom() -> Preterm
			= _ [Token::ParenL] preterm:preterm() _ [Token::ParenR] {preterm}
			/ _ [Token::SquareL] preterm:preterm() _ [Token::SquareR] {Preterm::Splice(preterm.into())}
			/ _ [Token::AngleL] preterm:preterm() _ [Token::AngleR] {Preterm::Quote(preterm.into())}
			/ identifier:identifier() {Preterm::Variable(identifier)}
			/ former:former() {Preterm::Former(former, vec![])}
			/ constructor:constructor() {Preterm::Constructor(constructor, vec![])}

		rule bound_spine_headed() -> (Name, Preterm)
			= _ [Token::Pipe] variable:identifier() _ [Token::Pipe] body:spine_headed() {(variable, body)}

		// Case arms.
		rule atomic_pattern() -> Pattern
			// TODO: Refactor longest match.
			= _ [Token::At] index:identifier() _ [Token::Period] witness:identifier() {Pattern::Witness {index, witness}}
			/ _ [Token::At] variable:identifier() {Pattern::Variable(variable)}

		rule pattern() -> Pattern
			= constructor:constructor() patterns:atomic_pattern()* {Pattern::Construction(constructor, patterns)}

		rule case() -> (Pattern, Preterm)
			= pattern:pattern() _ [Token::Arrow] preterm:preterm() {(pattern, preterm)}

		// Spines: projections, calls, and case-splits.
		#[cache_left_rec]
		rule spine() -> Preterm
			= former:former() arguments:atom()* {Preterm::Former(former, arguments)}
			/ constructor:constructor() arguments:atom()* {Preterm::Constructor(constructor, arguments)}
			/ callee:spine() argument:atom()
				{ Preterm::Call { callee: callee.into(), argument: argument.into() } }
			/ scrutinee:spine() _ [Token::TwoColon] motive:bound_spine_headed() _ [Token::CurlyL] (_ [Token::Pipe])? cases:case()**(_ [Token::Pipe]) _ [Token::CurlyR]
				{ Preterm::Split { scrutinee: scrutinee.into(), motive_parameter: motive.0, motive: motive.1.into(), cases} }
			/ spine:spine() projector:projector() { Preterm::Project(spine.into(), projector) }
			/ atom()

		#[cache]
		rule spine_headed() -> Preterm
			// TODO: Refactor to avoid caching?
			= _ [Token::Pipe] parameter:identifier() _ [Token::Pipe] body:spine_headed() {Preterm::Lambda { parameter, body: body.into() }}
			/ _ [Token::Pipe] parameter:identifier() _ [Token::Colon] base:spine_headed() _ [Token::Pipe] _ [Token::Arrow] right:spine_headed() {Preterm::Pi { parameter, base: base.into(), family: right.into() }}
			/ _ [Token::Pipe] parameter:identifier() _ [Token::Colon] base:spine_headed() _ [Token::Pipe] _ [Token::Amp] right:spine_headed() {Preterm::Sigma { parameter, base: base.into(), family: right.into() }}
			/ left:spine() _ [Token::Arrow] right:spine_headed() {Preterm::Pi { parameter: parser.interner.get_or_intern_static("_"), base: left.into(), family: right.into() }}
			/ left:spine() _ [Token::Amp] right:spine_headed() {Preterm::Sigma { parameter: parser.interner.get_or_intern_static("_"), base: left.into(), family: right.into() }}
			/ left:spine() _ [Token::Comma] right:spine_headed() {Preterm::Pair { basepoint: left.into(), fiberpoint: right.into() }}
			/ spine()

		rule preterm() -> Preterm
			= _ [Token::Keyword(Keyword::Let)] _ name:identifier() _ [Token::Colon] ty:spine_headed() _ [Token::Equal] argument:spine_headed() _ [Token::Semi] tail:preterm()
				{ Preterm::Let { assignee: name, ty: ty.into(), argument: argument.into(), tail: tail.into() }}
			/ _ [Token::Keyword(Keyword::Def)] name:identifier() _ [Token::Colon] ty:spine_headed() _ [Token::Equal] argument:spine_headed() _ [Token::Semi] tail:preterm()
				{ Preterm::Splice(Preterm::Let { assignee: name, ty: ty.into(), argument: argument.into(), tail: Preterm::Quote(tail.into()).into() }.into()) }
			/ spine_headed()

		pub rule program() -> Preterm
			= preterm:preterm() _ {preterm}
  }
}
