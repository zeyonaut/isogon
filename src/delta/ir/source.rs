use std::str::Chars;

use crate::delta::common::Field;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Token {
	Whitespace,
	Keyword(Keyword),
	Identifier,
	Number,
	Project(Field),
	LowDash,
	Amp,
	Bang,
	Hash,
	Pipe,
	Colon,
	TwoColon,
	Semi,
	Period,
	Comma,
	Equal,
	AngleL,
	AngleR,
	ParenL,
	ParenR,
	SquareL,
	SquareR,
	CurlyL,
	CurlyR,
	Ast,
	Tick,
	Arrow,
	At,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Keyword {
	Def,
	Let,
	Nat,
	Suc,
	Bool,
	True,
	False,
	CMax,
	C0,
	C1,
	Copy,
	WrapNew,
	Unwrap,
	WrapType,
	RcNew,
	UnRc,
	RcType,
	RPointer,
	RByte,
	RNat,
	RFun,
	RPair,
	RMax,
	RExp,
	RNone,
	Repr,
	Id,
	Refl,
}

pub struct LexError(pub usize, pub LexErrorKind);

pub enum LexErrorKind {
	UnrecognizedLexemePrefix,
	UnexpectedCharacter(&'static [char]),
	UnexpectedEnd(&'static [char]),
}

struct Scanner<'s> {
	len: usize,
	chars: Chars<'s>,
}

impl<'s> Scanner<'s> {
	pub fn new(source: &'s str) -> Self { Self { len: source.len(), chars: source.chars() } }

	pub fn position(&self) -> usize { self.len - self.chars.as_str().len() }

	pub fn previous_position(&self) -> usize { self.position() - 1 }

	pub fn next(&mut self) -> Option<(char, usize)> {
		let position = self.position();
		Some((self.chars.next()?, position))
	}

	pub fn pop(&mut self) -> Option<char> { self.chars.next() }

	pub fn peek(&mut self) -> Option<char> { self.chars.clone().next() }
}

pub struct LexedSource {
	pub tokens: Box<[Token]>,
	pub ranges: Box<[(usize, usize)]>,
}

impl LexedSource {
	fn keyword_or_identifier(string: &str) -> Token {
		use Token::*;

		use self::Keyword::*;
		match string {
			"def" => Keyword(Def),
			"let" => Keyword(Let),
			"suc" => Keyword(Suc),
			"nat" => Keyword(Nat),
			"bool" => Keyword(Bool),
			"true" => Keyword(True),
			"false" => Keyword(False),
			"cmax" => Keyword(CMax),
			"c0" => Keyword(C0),
			"c1" => Keyword(C1),
			"copy" => Keyword(Copy),
			"wrap" => Keyword(WrapNew),
			"unwrap" => Keyword(Unwrap),
			"Wrap" => Keyword(WrapType),
			"rc" => Keyword(RcNew),
			"unrc" => Keyword(UnRc),
			"RC" => Keyword(RcType),
			"rnone" => Keyword(RNone),
			"rpointer" => Keyword(RPointer),
			"rbyte" => Keyword(RByte),
			"rnat" => Keyword(RNat),
			"rfun" => Keyword(RFun),
			"rpair" => Keyword(RPair),
			"rmax" => Keyword(RMax),
			"rexp" => Keyword(RExp),
			"repr" => Keyword(Repr),
			"Id" => Keyword(Id),
			"refl" => Keyword(Refl),
			_ => Identifier,
		}
	}

	pub fn new(source: &str) -> Result<Self, LexError> {
		use LexErrorKind::*;
		use Token::*;
		let mut scanner = Scanner::new(source);
		let mut tokens = Vec::new();
		let mut ranges = Vec::new();
		while let Some((initial, start)) = scanner.next() {
			let token = match initial {
				' ' | '\n' | '\t' => {
					while let Some(' ' | '\n' | '\t') = scanner.peek() {
						scanner.pop();
					}
					Whitespace
				}
				'%' => {
					while let Some(c) = scanner.peek() {
						scanner.pop();
						if c == '\n' {
							break;
						}
					}
					Whitespace
				}
				'a'..='z' | 'A'..='Z' => {
					while let Some('a'..='z' | 'A'..='Z' | '0'..='9' | '_') = scanner.peek() {
						scanner.pop();
					}
					Self::keyword_or_identifier(&source[start..scanner.position()])
				}
				'0'..='9' => {
					while let Some('0'..='9') = scanner.peek() {
						scanner.pop();
					}
					Number
				}
				'/' => {
					const EXPECTED: [char; 2] = ['.', '!'];
					match scanner.pop() {
						Some('.') => Project(Field::Base),
						Some('!') => Project(Field::Fiber),
						Some(_) =>
							return Err(LexError(scanner.previous_position(), UnexpectedCharacter(&EXPECTED))),
						None => return Err(LexError(scanner.position(), UnexpectedEnd(&EXPECTED))),
					}
				}
				'_' => LowDash,
				'&' => Amp,
				'@' => At,
				'!' => Bang,
				'#' => Hash,
				'|' => Pipe,
				':' =>
					if let Some(':') = scanner.peek() {
						scanner.pop();
						TwoColon
					} else {
						Colon
					},
				';' => Semi,
				'.' => Period,
				',' => Comma,
				'=' => Equal,
				'<' => AngleL,
				'>' => AngleR,
				'(' => ParenL,
				')' => ParenR,
				'[' => SquareL,
				']' => SquareR,
				'{' => CurlyL,
				'}' => CurlyR,
				'*' => Ast,
				'\'' => Tick,
				'-' => {
					const EXPECTED: [char; 1] = ['>'];
					match scanner.pop() {
						Some('>') => Arrow,
						Some(_) =>
							return Err(LexError(scanner.previous_position(), UnexpectedCharacter(&EXPECTED))),
						None => return Err(LexError(scanner.position(), UnexpectedEnd(&EXPECTED))),
					}
				}
				_ => return Err(LexError(scanner.previous_position(), UnrecognizedLexemePrefix)),
			};
			tokens.push(token);
			ranges.push((start, scanner.position()));
		}

		debug_assert!(tokens.len() == ranges.len());
		Ok(Self { tokens: tokens.into_boxed_slice(), ranges: ranges.into_boxed_slice() })
	}
}
