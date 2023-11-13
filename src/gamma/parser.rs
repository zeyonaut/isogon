use std::iter::Peekable;

use lasso::{Rodeo, Spur};

use super::{
	common::Projection,
	lexer::{Lexeme, Lexer},
};
use crate::{gamma::lexer::Token, utility::bx};

pub type Name = Spur;

#[derive(Debug, Clone)]
pub enum StaticPreterm {
	Variable(Name),
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Lift(Box<DynamicPreterm>),
	Quote(Box<DynamicPreterm>),
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: Name, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
}

#[derive(Debug, Clone)]
pub enum DynamicPreterm {
	Variable(Name),
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Splice(Box<StaticPreterm>),
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: Name, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Project(Box<Self>, Projection),
}

pub struct Parser<'s> {
	source: &'s str,
	offset: usize,
	lexer: Peekable<Lexer<'s>>,
	pub interner: Rodeo,
}

impl<'s> Parser<'s> {
	pub fn new(source: &'s str) -> Self {
		Self { source, offset: 0, lexer: Lexer::new(source).peekable(), interner: Rodeo::new() }
	}

	pub fn peek_lexeme(&mut self) -> Option<Lexeme> {
		while let Some(lexeme) = self.lexer.peek() {
			use Token::*;
			if let Whitespace = lexeme.token {
				self.offset += lexeme.len;
				self.lexer.next();
				continue;
			} else {
				return Some(*lexeme);
			}
		}
		None
	}

	pub fn next_lexeme(&mut self) -> Option<(Lexeme, usize)> {
		for lexeme in self.lexer.by_ref() {
			let offset = self.offset;
			self.offset += lexeme.len;
			use Token::*;
			if let Whitespace = lexeme.token {
				continue;
			} else {
				return Some((lexeme, offset));
			}
		}
		None
	}

	pub fn identifier(&mut self, offset: usize, len: usize) -> Name {
		let span = &self.source[offset..offset + len];
		self.interner.get_or_intern(span)
	}

	pub fn consume(&mut self, token: Token) -> Option<()> {
		(self.next_lexeme()?.0.token == token).then_some(())
	}

	pub fn parse_static(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;

		let Lexeme { token, len } = self.peek_lexeme()?;
		match token {
			Identifier => {
				let span = &self.source[self.offset..self.offset + len];
				match span {
					"let" => {
						self.next_lexeme();
						let name = {
							let (Lexeme { token: Identifier, len }, offset) = self.next_lexeme()? else {
								return None;
							};
							self.identifier(offset, len)
						};
						self.consume(Colon)?;
						let ty = self.parse_static()?;
						self.consume(Equal)?;
						let argument = self.parse_static()?;
						self.consume(Semi)?;
						let tail = self.parse_static()?;

						Some(Let { assignee: name, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) })
					}
					_ => self.parse_static_atom_headed(),
				}
			}
			Pipe => {
				self.next_lexeme();
				let name = {
					let (Lexeme { token: Identifier, len }, offset) = self.next_lexeme()? else {
						return None;
					};
					self.identifier(offset, len)
				};
				match self.peek_lexeme()?.token {
					Pipe => {
						self.next_lexeme();
						let body = self.parse_static()?;
						Some(Lambda { parameter: name, body: bx!(body) })
					}
					Colon => {
						self.next_lexeme();
						let base = self.parse_static()?;
						self.consume(Pipe)?;
						self.consume(Arrow)?;
						let family = self.parse_static()?;
						Some(Pi { parameter: name, base: bx!(base), family: bx!(family) })
					}
					_ => None,
				}
			}
			_ => self.parse_static_atom_headed(),
		}
	}

	pub fn parse_dynamic(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;

		let Lexeme { token, len } = self.peek_lexeme()?;
		match token {
			Identifier => {
				let span = &self.source[self.offset..self.offset + len];
				match span {
					"let" => {
						self.next_lexeme();
						let name = {
							let (Lexeme { token: Identifier, len }, offset) = self.next_lexeme()? else {
								return None;
							};
							self.identifier(offset, len)
						};
						self.consume(Colon)?;
						let ty = self.parse_dynamic()?;
						self.consume(Equal)?;
						let argument = self.parse_dynamic()?;
						self.consume(Semi)?;
						let tail = self.parse_dynamic()?;

						Some(Let { assignee: name, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) })
					}
					"def" => {
						self.next_lexeme();
						let name = {
							let (Lexeme { token: Identifier, len }, offset) = self.next_lexeme()? else {
								return None;
							};
							self.identifier(offset, len)
						};
						self.consume(Colon)?;
						let ty = self.parse_static()?;
						self.consume(Equal)?;
						let argument = self.parse_static()?;
						self.consume(Semi)?;
						let tail = self.parse_dynamic()?;

						Some(Splice(bx!(StaticPreterm::Let {
							assignee: name,
							ty: bx!(ty),
							argument: bx!(argument),
							tail: bx!(StaticPreterm::Quote(bx!(tail)))
						})))
					}
					_ => self.parse_dynamic_atom_headed(),
				}
			}
			Pipe => {
				self.next_lexeme();
				let name = {
					let (Lexeme { token: Identifier, len }, offset) = self.next_lexeme()? else {
						return None;
					};
					self.identifier(offset, len)
				};
				match self.peek_lexeme()?.token {
					Pipe => {
						self.next_lexeme();
						let body = self.parse_dynamic()?;
						Some(Lambda { parameter: name, body: bx!(body) })
					}
					Colon => {
						self.next_lexeme();
						let base = self.parse_dynamic()?;
						self.consume(Pipe)?;
						match self.next_lexeme()?.0.token {
							Arrow => {
								let family = self.parse_dynamic()?;
								Some(Pi { parameter: name, base: bx!(base), family: bx!(family) })
							}
							Amp => {
								let family = self.parse_dynamic()?;
								Some(Sigma { parameter: name, base: bx!(base), family: bx!(family) })
							}
							_ => None,
						}
					}
					_ => None,
				}
			}
			_ => self.parse_dynamic_atom_headed(),
		}
	}

	pub fn parse_static_atom_headed(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;
		let term = self.parse_static_spine()?;
		if let Some(Lexeme { token: Arrow, len: _ }) = self.peek_lexeme() {
			self.next_lexeme();
			let family = self.parse_static()?;
			Some(Pi { parameter: self.interner.get_or_intern_static("_"), base: bx!(term), family: bx!(family) })
		} else {
			Some(term)
		}
	}

	pub fn parse_dynamic_atom_headed(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;
		let term = self.parse_dynamic_spine()?;
		match self.peek_lexeme().map(|lexeme| lexeme.token) {
			Some(Arrow) => {
				self.next_lexeme();
				let family = self.parse_dynamic()?;
				Some(Pi {
					parameter: self.interner.get_or_intern_static("_"),
					base: bx!(term),
					family: bx!(family),
				})
			}
			Some(Amp) => {
				self.next_lexeme();
				let family = self.parse_dynamic()?;
				Some(Sigma {
					parameter: self.interner.get_or_intern_static("_"),
					base: bx!(term),
					family: bx!(family),
				})
			}
			Some(Comma) => {
				self.next_lexeme();
				let rest = self.parse_dynamic_atom_headed()?;
				Some(Pair { basepoint: bx!(term), fiberpoint: bx!(rest) })
			}
			_ => Some(term),
		}
	}

	pub fn parse_static_spine(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;
		let mut term = self.parse_static_atom()?;
		while let Some(Lexeme { token, len: _ }) = self.peek_lexeme() {
			match token {
				Tick | SquareL | ParenL | Ast | Identifier => {
					let atom = self.parse_static_atom()?;
					term = Apply { scrutinee: bx!(term), argument: bx!(atom) };
				}
				_ => break,
			}
		}
		Some(term)
	}

	pub fn parse_dynamic_spine(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;
		let mut term = self.parse_dynamic_atom()?;
		while let Some(Lexeme { token, len: _ }) = self.peek_lexeme() {
			match token {
				SquareL | ParenL | Ast | Identifier => {
					let atom = self.parse_dynamic_atom()?;
					term = Apply { scrutinee: bx!(term), argument: bx!(atom) };
				}
				Token::Project(projection) => {
					self.next_lexeme();
					term = DynamicPreterm::Project(bx!(term), projection);
				}
				_ => break,
			}
		}
		Some(term)
	}

	pub fn parse_static_atom(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;
		let (Lexeme { token, len }, offset) = self.next_lexeme()?;
		let term = match token {
			Tick => {
				let term = self.parse_dynamic_atom()?;
				Lift(bx!(term))
			}
			SquareL => {
				let term = self.parse_dynamic()?;
				self.consume(SquareR)?;
				Quote(bx!(term))
			}
			ParenL => {
				let term = self.parse_static()?;
				self.consume(ParenR)?;
				term
			}
			Ast => Universe,
			Identifier => Variable(self.identifier(offset, len)),
			_ => return None,
		};
		Some(term)
	}

	fn parse_dynamic_atom(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;
		let (Lexeme { token, len }, offset) = self.next_lexeme()?;
		let term = match token {
			SquareL => {
				let term = self.parse_static()?;
				self.consume(SquareR)?;
				Splice(bx!(term))
			}
			ParenL => {
				let term = self.parse_dynamic()?;
				self.consume(ParenR)?;
				term
			}
			Ast => Universe,
			Identifier => Variable(self.identifier(offset, len)),
			_ => return None,
		};
		Some(term)
	}
}
