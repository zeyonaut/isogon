use lasso::{Rodeo, RodeoResolver};

use crate::delta::{
	common::{any_bind, bind, AnyBinder, Cost, Cpy, Name, ReprAtom},
	ir::{
		presyntax::{Constructor, Expression, Former, ParsedLabel, ParsedProgram, Pattern, Preterm, Projector},
		source::{Keyword, LexError, LexErrorKind, LexedSource, Pragma, Token},
	},
};

/// Parses a dynamic preterm from a source string.
pub fn parse(source: &str) -> (LexedSource, ParsedProgram, RodeoResolver) {
	let lexed_source = match LexedSource::new(source) {
		Ok(lexed_source) => lexed_source,
		Err(lex_error) => {
			report_line_error(source, (lex_error.0, lex_error.0 + 1), &format_lex_error(source, lex_error));
			panic!();
		}
	};
	let mut parser = Parser { source, interner: Rodeo::new(), ranges: lexed_source.ranges.clone() };
	let program = match presyntax_parse::program(&lexed_source.tokens, &mut parser) {
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

	(lexed_source, program, parser.interner.into_resolver())
}
pub fn format_lex_error(source: &str, LexError(location, kind): LexError) -> String {
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

pub fn report_line_error(source: &str, range: (usize, usize), error_string: &str) {
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

		rule parameter() -> ParsedLabel
			= locus:position!() name:identifier() {ParsedLabel { locus, label: Some(name) }}

		rule optional_parameter() -> ParsedLabel
			= locus:position!() label:(name:identifier() {Some(name)} / [Token::LowDash] {None}) {ParsedLabel { locus, label }}

		rule cost_annotation() -> Cost
			= [Token::SquareL] _ cost:([Token::Ast] {Cost::Inf} / number:number() {Cost::Fin(number)}) _ [Token::SquareR] {cost}

		rule finite_grade_annotation() -> usize
			= [Token::SquareL] _ number:number() _ [Token::SquareR] {number}

		rule former() -> Former
			= [Token::Tick] {Former::Lift}
			/ [Token::Keyword(Keyword::Copy)] {Former::Copy}
			/ [Token::Keyword(Keyword::Repr)] {Former::Repr}
			// Repeated programs.
			/ [Token::Ast] {Former::Universe}
			/ [Token::Bang] grade:cost_annotation() {Former::Exp(grade)}
			// Enumerated numbers.
			/ [Token::Keyword(Keyword::Bool)] {Former::Enum(2)}
			/ [Token::Hash] card:number() { assert!(card <= 256); Former::Enum(card as u16)}
			// Paths.
			/ [Token::Keyword(Keyword::Id)] {Former::Id}
			// Natural numbers.
			/ [Token::Keyword(Keyword::Nat)] {Former::Nat}
			// Wrappers.
			/ [Token::Keyword(Keyword::Bx)] {Former::Bx}
			/ [Token::Keyword(Keyword::Wrap)] {Former::Wrap}

		rule constructor() -> Constructor
			= [Token::Keyword(Keyword::C0)] {Constructor::Cpy(Cpy::Tr)}
			/ [Token::Keyword(Keyword::C1)] {Constructor::Cpy(Cpy::Nt)}
			/ [Token::Keyword(Keyword::CMax)] {Constructor::CpyMax}
			/ [Token::Keyword(Keyword::RPtr)] {Constructor::ReprAtom(Some(ReprAtom::Ptr))}
			/ [Token::Keyword(Keyword::RByte)] {Constructor::ReprAtom(Some(ReprAtom::Byte))}
			/ [Token::Keyword(Keyword::RNat)] {Constructor::ReprAtom(Some(ReprAtom::Nat))}
			/ [Token::Keyword(Keyword::RFun)] {Constructor::ReprAtom(Some(ReprAtom::Fun))}
			/ [Token::Keyword(Keyword::RNone)] {Constructor::ReprAtom(None)}
			/ [Token::Keyword(Keyword::RPair)] {Constructor::ReprPair}
			/ [Token::Keyword(Keyword::RMax)] {Constructor::ReprMax}
			// Repeated programs.
			/ [Token::Keyword(Keyword::RExp)] grade:finite_grade_annotation() {Constructor::ReprExp(grade)}
			/ [Token::At] grade:cost_annotation() {Constructor::Exp(grade)}
			// Enumerated numbers.
			/ number:number() [Token::LowDash] card:number() {assert!(card <= 256 && number < card); Constructor::Enum(card as _, number as _)}
			/ [Token::Keyword(Keyword::False)] {Constructor::Enum(2, 0)}
			/ [Token::Keyword(Keyword::True)] {Constructor::Enum(2, 1)}
			// Paths.
			/ [Token::Keyword(Keyword::Refl)] {Constructor::Refl}
			// Natural numbers.
			/ number:number() {Constructor::Num(number)}
			/ [Token::Keyword(Keyword::Suc)] {Constructor::Suc}
			// Wrappers.
			/ [Token::Keyword(Keyword::BxValue)] {Constructor::Bx}
			/ [Token::Keyword(Keyword::WrapValue)] {Constructor::Wrap}

		rule projector() -> Projector
			= [Token::Keyword(Keyword::ExpProject)] {Projector::Exp}
			/ [Token::Keyword(Keyword::BxProject)] {Projector::Bx}
			/ [Token::Keyword(Keyword::WrapProject)] {Projector::Wrap}
			/ [Token::Project(projection)] {Projector::Field(projection)}

		rule atom() -> Expression
			= [Token::ParenL] _ preterm:preterm() _ [Token::ParenR] {preterm}
			/ init:position!() preterm:(
				  [Token::AngleL] _ preterm:preterm() _ [Token::AngleR] {Preterm::SwitchLevel(preterm.into())}
				/ identifier:identifier() {Preterm::Variable(identifier)}
				/ former:former() {Preterm::Former(former, vec![])}
				/ constructor:constructor() {Preterm::Constructor(constructor, vec![])}
			) fini:position!() {preterm.at((init, fini))}

		rule bound_spine_headed() -> AnyBinder<ParsedLabel, Box<Expression>>
			= [Token::Pipe] _ variables:(variable:optional_parameter())**[Token::Period] _ [Token::Pipe] _ body:spine_headed() {any_bind(variables, body)}

		// Case arms.
		rule atomic_pattern() -> Pattern<ParsedLabel>
			= [Token::At] index:optional_parameter() _ [Token::Period] witness:optional_parameter() {Pattern::Witness {index, witness}}
			/ [Token::At] variable:optional_parameter() {Pattern::Variable(variable)}

		rule pattern() -> Pattern<ParsedLabel>
			= constructor:constructor() patterns:(_ p:atomic_pattern() {p})* {Pattern::Construction(constructor, patterns)}

		rule case() -> (Pattern<ParsedLabel>, Expression)
			= pattern:pattern() _ [Token::Arrow] _ preterm:preterm() {(pattern, preterm)}

		// Spines: projections, calls, and case-splits.
		#[cache_left_rec]
		rule spine() -> Expression
			= init:position!() preterm:(
				  former:former() arguments:(_ a:atom() {a})* {Preterm::Former(former, arguments)}
				/ constructor:constructor() arguments:(_ a:atom() {a})* {Preterm::Constructor(constructor, arguments)}
				// Function calls.
				/ callee:spine() _ argument:atom()
					{ Preterm::Call { callee: callee.into(), argument: argument.into() } }
				// Case splits.
				/ scrutinee:spine() _ cast:([Token::Keyword(Keyword::Cast)] {})? _ [Token::TwoColon] _ motive:bound_spine_headed() _ [Token::CurlyL] (_ [Token::Pipe])? _ cases:case()**(_ [Token::Pipe] _) _ [Token::CurlyR]
					{ Preterm::Split { scrutinee: scrutinee.into(), is_cast: cast.is_some(), motive, cases} }
				// Projections.
				/ spine:spine() _ projector:projector() { Preterm::Project(spine.into(), projector) }
			) fini:position!() {preterm.at((init, fini))}
			/ atom()

		#[cache]
		rule spine_headed() -> Expression
			= init:position!() preterm:(
				  [Token::Pipe] _ grade:(finite_grade_annotation())? _ parameter:optional_parameter() _ [Token::Pipe] _ body:spine_headed() {Preterm::Lambda { grade: grade.unwrap_or(parameter.label.is_some() as _), body: bind([parameter], body) }}
				/ [Token::Pipe] _ grade:(finite_grade_annotation())? _ parameter:optional_parameter() _ [Token::Colon] _ base:spine_headed() _ [Token::Pipe] _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { grade: grade.unwrap_or(1), base: base.into(), family: bind([parameter], right) }}
				/ locus:position!() left:spine() _ grade:(finite_grade_annotation())? _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { grade: grade.unwrap_or(1), base: left.into(), family: bind([ParsedLabel {locus, label: None}], right) }}
				/ [Token::Pipe] _ parameter:optional_parameter() _ [Token::Colon] _ base:spine_headed() _ [Token::Pipe] _ [Token::Amp] _ right:spine_headed() {Preterm::Sg { base: base.into(), family: bind([parameter], right) }}
				/ locus:position!() left:spine() _ [Token::Amp] _ right:spine_headed() {Preterm::Sg { base: left.into(), family: bind([ParsedLabel {locus, label: None}], right) }}
				/ left:spine() _ [Token::Comma] _ right:spine_headed() {Preterm::Pair { basepoint: left.into(), fiberpoint: right.into() }}
			) fini:position!() {preterm.at((init, fini))}
			/ spine()

		rule preterm() -> Expression
			= init:position!() preterm:(
				is_meta:([Token::Keyword(Keyword::Let)] {false} / [Token::Keyword(Keyword::Def)] {true})
					_ grade:(cost_annotation())? _ name:optional_parameter() _ [Token::Colon] _ ty:spine_headed() _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm()
				{ Preterm::Let { is_meta, grade, ty: ty.into(), argument: argument.into(), tail: bind([name], tail) }}
				/ [Token::Keyword(Keyword::Let)] _ grade:(cost_annotation())? _ [Token::At] grade_argument:cost_annotation() _ name:optional_parameter() _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm() {
					Preterm::ExpLet { grade, grade_argument, argument: argument.into(), tail: bind([name], tail) }
				}
				/ [Token::Keyword(Keyword::Let)] _ grade:(finite_grade_annotation())? _ [Token::ParenL] _ a:parameter() _ [Token::Comma] _ b:parameter() _ [Token::ParenR] _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm() {
					Preterm::SgLet { grade: grade.unwrap_or(1), argument: argument.into(), tail: bind([a, b], tail) }
				}
			) fini:position!() {preterm.at((init, fini))}
			/ spine_headed()

		rule pragma_fragment() -> u8
			= [Token::Pragma(Pragma::Fragment)] _ number:number() {(number > 0) as u8}
			/ {1}

		pub rule program() -> ParsedProgram
			= _ fragment:pragma_fragment() _ expr:preterm() _ {ParsedProgram {fragment, expr}}

  }
}
