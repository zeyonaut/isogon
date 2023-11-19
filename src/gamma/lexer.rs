use std::str::Chars;

use super::common::Projection;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Token {
	Whitespace,
	Keyword(Keyword),
	Identifier,
	Number,
	Project(Projection),
	Amp,
	Pipe,
	Colon,
	TwoColon,
	Semi,
	Comma,
	Equal,
	ParenL,
	ParenR,
	SquareL,
	SquareR,
	CurlyL,
	CurlyR,
	Ast,
	Tick,
	Arrow,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Keyword {
	Def,
	Let,
	Nat,
	Suc,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Lexeme {
	pub token: Token,
	pub range: (usize, usize),
}

impl Lexeme {
	pub fn new(token: Token, range: (usize, usize)) -> Self {
		Self { token, range }
	}
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
	pub fn new(source: &'s str) -> Self {
		Self { len: source.len(), chars: source.chars() }
	}

	pub fn position(&self) -> usize {
		self.len - self.chars.as_str().len()
	}

	pub fn previous_position(&self) -> usize {
		self.position() - 1
	}

	pub fn next(&mut self) -> Option<(char, usize)> {
		let position = self.position();
		Some((self.chars.next()?, position))
	}

	pub fn pop(&mut self) -> Option<char> {
		self.chars.next()
	}

	pub fn peek(&mut self) -> Option<char> {
		self.chars.clone().next()
	}
}

pub struct LexedSource {
	pub lexemes: Vec<Lexeme>,
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
			_ => Identifier,
		}
	}

	pub fn new(source: &str) -> Result<Self, LexError> {
		use LexErrorKind::*;
		use Token::*;
		let mut scanner = Scanner::new(source);
		let mut lexemes = Vec::new();
		while let Some((initial, start)) = scanner.next() {
			let token = match initial {
				' ' | '\n' | '\t' => {
					while let Some(' ' | '\n' | '\t') = scanner.peek() {
						scanner.pop();
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
						Some('.') => Project(Projection::Base),
						Some('!') => Project(Projection::Fiber),
						Some(_) =>
							return Err(LexError(scanner.previous_position(), UnexpectedCharacter(&EXPECTED))),
						None => return Err(LexError(scanner.previous_position(), UnexpectedEnd(&EXPECTED))),
					}
				}
				'&' => Amp,
				'|' => Pipe,
				':' =>
					if let Some(':') = scanner.peek() {
						scanner.pop();
						TwoColon
					} else {
						Colon
					},
				';' => Semi,
				',' => Comma,
				'=' => Equal,
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
						None => return Err(LexError(scanner.previous_position(), UnexpectedEnd(&EXPECTED))),
					}
				}
				_ => return Err(LexError(scanner.previous_position(), UnrecognizedLexemePrefix)),
			};
			lexemes.push(Lexeme::new(token, (start, scanner.position())))
		}

		Ok(Self { lexemes })
	}
}
