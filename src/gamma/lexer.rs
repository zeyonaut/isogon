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

#[derive(Copy, Clone, Debug)]
pub struct Lexeme {
	pub token: Token,
	pub len: usize,
}

impl Lexeme {
	pub fn new(token: Token, len: usize) -> Self {
		Self { token, len }
	}
}

pub struct Lexer<'s> {
	source: &'s str,
	chars: Chars<'s>,
	len_remaining: usize,
}

impl<'s> Lexer<'s> {
	pub fn new(source: &'s str) -> Self {
		Self { source, chars: source.chars(), len_remaining: source.len() }
	}

	fn next_char(&mut self) -> Option<char> {
		self.chars.next()
	}

	fn peek_char(&mut self) -> Option<char> {
		self.chars.clone().next()
	}

	fn advance_len(&mut self) -> usize {
		let len = self.len_remaining;
		self.len_remaining = self.chars.as_str().len();
		len - self.len_remaining
	}

	fn keyword_or_identifier(&self) -> Token {
		use Token::*;

		use self::Keyword::*;
		match &self.source
			[self.source.len() - self.len_remaining..self.source.len() - self.chars.as_str().len()]
		{
			"def" => Keyword(Def),
			"let" => Keyword(Let),
			"suc" => Keyword(Suc),
			"nat" => Keyword(Nat),
			_ => Identifier,
		}
	}
}

impl<'s> Iterator for Lexer<'s> {
	type Item = Lexeme;

	fn next(&mut self) -> Option<Self::Item> {
		use Token::*;
		let initial = self.next_char()?;
		let token = match initial {
			' ' | '\n' | '\t' => {
				while let Some(' ' | '\n' | '\t') = self.peek_char() {
					self.next_char();
				}
				Whitespace
			}
			'a'..='z' | 'A'..='Z' => {
				while let Some('a'..='z' | 'A'..='Z' | '0'..='9' | '_') = self.peek_char() {
					self.next_char();
				}
				self.keyword_or_identifier()
			}
			'0'..='9' => {
				while let Some('0'..='9') = self.peek_char() {
					self.next_char();
				}
				Number
			}
			'/' => match self.next_char()? {
				'.' => Project(Projection::Base),
				'!' => Project(Projection::Fiber),
				_ => panic!("unrecognized character"),
			},
			'&' => Amp,
			'|' => Pipe,
			':' =>
				if let Some(':') = self.peek_char() {
					self.next_char();
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
			'-' if Some('>') == self.peek_char() => {
				self.next_char();
				Arrow
			}
			_ => panic!("unrecognized character"),
		};
		Some(Lexeme::new(token, self.advance_len()))
	}
}
