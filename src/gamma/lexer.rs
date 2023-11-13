use std::str::Chars;

use super::common::Projection;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Token {
	Whitespace,
	Identifier,
	Project(Projection),
	Amp,
	Pipe,
	Colon,
	Semi,
	Comma,
	Equal,
	ParenL,
	ParenR,
	SquareL,
	SquareR,
	Ast,
	Tick,
	Arrow,
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
	chars: Chars<'s>,
	len_remaining: usize,
}

impl<'s> Lexer<'s> {
	pub fn new(source: &'s str) -> Self {
		Self { chars: source.chars(), len_remaining: source.len() }
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
				Identifier
			}
			'/' => match self.next_char()? {
				'.' => Project(Projection::Base),
				'!' => Project(Projection::Fiber),
				_ => panic!("unrecognized character"),
			},
			'&' => Amp,
			'|' => Pipe,
			':' => Colon,
			';' => Semi,
			',' => Comma,
			'=' => Equal,
			'(' => ParenL,
			')' => ParenR,
			'[' => SquareL,
			']' => SquareR,
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
