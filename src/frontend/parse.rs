use lasso::{Rodeo, RodeoResolver};
use peg::error::ParseError;

use crate::{
	common::{any_bind, bind, AnyBinder, Cost, Cpy, Fragment, Name, ReprAtom},
	ir::{
		presyntax::{Constructor, Expression, Former, ParsedLabel, ParsedProgram, Pattern, Preterm, Projector},
		tokenized::{Keyword, Pragma, Token, TokenizedSource},
	},
};

/// Parses a dynamic preterm from a source string.
pub fn parse(source: &TokenizedSource) -> Result<(ParsedProgram, RodeoResolver), ParseError<usize>> {
	let mut parser = Parser { source: source.source, interner: Rodeo::new(), ranges: source.ranges.clone() };
	Ok((presyntax_parse::program(&source.tokens, &mut parser)?, parser.interner.into_resolver()))
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

	fn number64(&self, token_index: usize) -> Option<u64> {
		let range = self.ranges[token_index];
		let span = &self.source[range.0..range.1];
		span.parse::<u64>().ok()
	}
}

peg::parser! {
  grammar presyntax_parse(parser: &mut Parser) for [Token] {
		rule _ = [Token::Whitespace]*

		rule identifier() -> Name
			= pos:position!() [Token::Identifier] {parser.identifier(pos)}

		rule number() -> usize
			= pos:position!() [Token::Number] {parser.number(pos).unwrap()}

		rule number64() -> u64
		= pos:position!() [Token::Number] {parser.number64(pos).unwrap()}

		rule parameter() -> ParsedLabel
			= locus:position!() name:identifier() {ParsedLabel { locus, label: Some(name) }}

		rule optional_parameter() -> ParsedLabel
			= locus:position!() label:(name:identifier() {Some(name)} / [Token::LowDash] {None}) {ParsedLabel { locus, label }}

		rule cost_annotation() -> Cost
			= [Token::SquareL] _ cost:([Token::Ast] {Cost::Inf} / number:number64() {Cost::Fin(number)}) _ [Token::SquareR] {cost}

		rule finite_grade_annotation() -> u64
			= [Token::SquareL] _ number:number64() _ [Token::SquareR] {number}

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
			/ number:number64() {Constructor::Num(number)}
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
				  [Token::Pipe] _ parameter:optional_parameter() _ [Token::Pipe] _ body:spine_headed() {Preterm::Lambda { body: bind([parameter], body) }}
				/ [Token::Pipe] _ parameter:optional_parameter() _ [Token::Colon] _ base:spine_headed() _ [Token::Pipe] _ fragment:[Token::At]? _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { fragment: if fragment.is_some() {Fragment::Logical} else {Fragment::Material}, base: base.into(), family: bind([parameter], right) }}
				/ locus:position!() left:spine() _ fragment:[Token::At]? _ [Token::Arrow] _ right:spine_headed() {Preterm::Pi { fragment: if fragment.is_some() {Fragment::Logical} else {Fragment::Material}, base: left.into(), family: bind([ParsedLabel {locus, label: None}], right) }}
				/ [Token::Pipe] _ parameter:optional_parameter() _ [Token::Colon] _ base:spine_headed() _ [Token::Pipe] _ [Token::Amp] _ right:spine_headed() {Preterm::Sg { base: base.into(), family: bind([parameter], right) }}
				/ locus:position!() left:spine() _ [Token::Amp] _ right:spine_headed() {Preterm::Sg { base: left.into(), family: bind([ParsedLabel {locus, label: None}], right) }}
				/ left:spine() _ [Token::Comma] _ right:spine_headed() {Preterm::Pair { basepoint: left.into(), fiberpoint: right.into() }}
			) fini:position!() {preterm.at((init, fini))}
			/ spine()

		rule preterm() -> Expression
			= init:position!() preterm:(
				is_meta:([Token::Keyword(Keyword::Let)] {false} / [Token::Keyword(Keyword::Def)] {true})
					_ grade:(cost_annotation())? _ name:optional_parameter() _ ty:([Token::Colon] _ ty:spine_headed() {ty})? _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm()
				{ Preterm::Let { is_meta, grade, ty: ty.map(Box::new), argument: argument.into(), tail: bind([name], tail) }}
				/ [Token::Keyword(Keyword::Let)] _ grade:(cost_annotation())? _ [Token::At] grade_argument:cost_annotation() _ name:optional_parameter() _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm() {
					Preterm::ExpLet { grade, grade_argument, argument: argument.into(), tail: bind([name], tail) }
				}
				/ [Token::Keyword(Keyword::Let)] _ grade:(finite_grade_annotation())? _ [Token::ParenL] _ a:parameter() _ [Token::Comma] _ b:parameter() _ [Token::ParenR] _ [Token::Equal] _ argument:spine_headed() _ [Token::Semi] _ tail:preterm() {
					Preterm::SgLet { grade: grade.unwrap_or(1), argument: argument.into(), tail: bind([a, b], tail) }
				}
			) fini:position!() {preterm.at((init, fini))}
			/ spine_headed()

		rule pragma_fragment() -> Fragment
			= [Token::Pragma(Pragma::Fragment)] _ number:number() {if number > 0 {Fragment::Material} else {Fragment::Logical}}
			/ {Fragment::Material}

		pub rule program() -> ParsedProgram
			= _ fragment:pragma_fragment() _ expr:preterm() _ {ParsedProgram {fragment, expr}}

  }
}
