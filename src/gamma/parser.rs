use lasso::Rodeo;

use super::{
	common::{bind, Binder, Copyability, Name, Projection},
	lexer::{Keyword, LexedSource, Lexeme, Token},
};
use crate::utility::bx;

#[derive(Debug, Clone)]
pub enum StaticPreterm {
	Variable(Name),
	Let {
		assignee: Name,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Box<Self>,
	},
	Lift(Box<DynamicPreterm>),
	Quote(Box<DynamicPreterm>),
	Universe,
	Pi {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Lambda {
		parameter: Name,
		body: Box<Self>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive_parameter: Name,
		motive: Box<Self>,
		case_nil: Box<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Box<Self>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
	CopyabilityType,
	Copyability(Copyability),
	MaxCopyability(Box<Self>, Box<Self>),
}

#[derive(Debug, Clone)]
pub enum DynamicPreterm {
	Variable(Name),
	Let {
		assignee: Name,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Box<Self>,
	},
	Splice(Box<StaticPreterm>),
	Universe {
		copyability: Box<StaticPreterm>,
	},
	Pi {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Lambda {
		parameter: Name,
		body: Box<Self>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive_parameter: Name,
		motive: Box<Self>,
		case_nil: Box<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Box<Self>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
}

pub struct Parser<'s> {
	source: &'s str,
	lexeme_index: usize,
	lexed_source: LexedSource,
	pub interner: Rodeo,
}

impl<'s> Parser<'s> {
	pub fn new(source: &'s str, lexed_source: LexedSource) -> Self {
		Self { source, lexeme_index: 0, lexed_source, interner: Rodeo::new() }
	}

	pub fn peek_lexeme(&mut self) -> Option<Lexeme> {
		while let Some(lexeme) = self.lexed_source.lexemes.get(self.lexeme_index) {
			use Token::*;
			if let Whitespace = lexeme.token {
				self.lexeme_index += 1;
			} else {
				return Some(*lexeme);
			}
		}
		None
	}

	pub fn next_lexeme(&mut self) -> Option<Lexeme> {
		while let Some(lexeme) = self.lexed_source.lexemes.get(self.lexeme_index) {
			use Token::*;
			self.lexeme_index += 1;
			if let Whitespace = lexeme.token {
				continue;
			} else {
				return Some(*lexeme);
			}
		}
		None
	}

	pub fn identifier(&mut self, range: (usize, usize)) -> Name {
		let span = &self.source[range.0..range.1];
		self.interner.get_or_intern(span)
	}

	#[must_use]
	pub fn parse_identifier(&mut self) -> Option<Name> {
		let Lexeme { token: Token::Identifier, range } = self.next_lexeme()? else {
			return None;
		};
		Some(self.identifier(range))
	}

	#[must_use]
	pub fn consume(&mut self, token: Token) -> Option<()> {
		(self.next_lexeme()?.token == token).then_some(())
	}

	pub fn parse_static(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;

		use self::Keyword;

		let Lexeme { token, .. } = self.peek_lexeme()?;
		match token {
			Keyword(Keyword::Let) => {
				self.next_lexeme();
				let name = self.parse_identifier()?;
				self.consume(Colon)?;
				let ty = self.parse_static()?;
				self.consume(Equal)?;
				let argument = self.parse_static()?;
				self.consume(Semi)?;
				let tail = self.parse_static()?;

				Some(Let { assignee: name, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) })
			}
			Pipe => {
				self.next_lexeme();
				let name = self.parse_identifier()?;
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

		use self::Keyword;

		let Lexeme { token, .. } = self.peek_lexeme()?;
		match token {
			Keyword(Keyword::Let) => {
				self.next_lexeme();
				let name = self.parse_identifier()?;
				self.consume(Colon)?;
				let ty = self.parse_dynamic()?;
				self.consume(Equal)?;
				let argument = self.parse_dynamic()?;
				self.consume(Semi)?;
				let tail = self.parse_dynamic()?;

				Some(Let { assignee: name, ty: bx!(ty), argument: bx!(argument), tail: bx!(tail) })
			}
			Keyword(Keyword::Def) => {
				self.next_lexeme();
				let name = self.parse_identifier()?;
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
			Pipe => {
				self.next_lexeme();
				let name = self.parse_identifier()?;
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
						match self.next_lexeme()?.token {
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
		match self.peek_lexeme().map(|lexeme| lexeme.token) {
			Some(Arrow) => {
				self.next_lexeme();
				let family = self.parse_static()?;
				Some(Pi {
					parameter: self.interner.get_or_intern_static("_"),
					base: bx!(term),
					family: bx!(family),
				})
			}
			Some(Amp) => {
				self.next_lexeme();
				let family = self.parse_static()?;
				Some(Sigma {
					parameter: self.interner.get_or_intern_static("_"),
					base: bx!(term),
					family: bx!(family),
				})
			}
			Some(Comma) => {
				self.next_lexeme();
				let rest = self.parse_static_atom_headed()?;
				Some(Pair { basepoint: bx!(term), fiberpoint: bx!(rest) })
			}
			_ => Some(term),
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

		let Lexeme { token, .. } = self.peek_lexeme()?;

		let mut term = match token {
			Keyword(self::Keyword::Suc) => {
				self.next_lexeme();
				Suc(bx!(self.parse_static_atom()?))
			}
			Keyword(self::Keyword::CMax) => {
				self.next_lexeme();
				MaxCopyability(bx!(self.parse_static_atom()?), bx!(self.parse_static_atom()?))
			}
			_ => self.parse_static_atom()?,
		};

		while let Some(Lexeme { token, .. }) = self.peek_lexeme() {
			match token {
				_ if Self::is_static_atom_start(token) => {
					term = Apply { scrutinee: bx!(term), argument: bx!(self.parse_static_atom()?) };
				}
				Token::Project(projection) => {
					self.next_lexeme();
					term = StaticPreterm::Project(bx!(term), projection);
				}
				TwoColon => {
					self.next_lexeme();
					if let Some(Keyword(self::Keyword::Bool)) = self.peek_lexeme().map(|x| x.token) {
						self.next_lexeme();
						self.consume(Pipe)?;
						let motive_parameter = self.parse_identifier()?;
						self.consume(Pipe)?;
						let motive = self.parse_static()?;
						self.consume(CurlyL)?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::False))?;
						self.consume(Arrow)?;
						let case_false = self.parse_static()?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::True))?;
						self.consume(Arrow)?;
						let case_true = self.parse_static()?;
						self.consume(CurlyR)?;
						term = StaticPreterm::CaseBool {
							scrutinee: bx!(term),
							motive: bind([motive_parameter], bx!(motive)),
							case_false: bx!(case_false),
							case_true: bx!(case_true),
						}
					} else {
						self.consume(Pipe)?;
						let motive_parameter = self.parse_identifier()?;
						self.consume(Pipe)?;
						let motive = self.parse_static()?;
						self.consume(CurlyL)?;
						self.consume(Pipe)?;
						{
							let Lexeme { token: Number, range } = self.next_lexeme()? else {
								return None;
							};
							(&self.source[range.0..range.1] == "0").then_some(())? // TODO: Wrap this.
						}
						self.consume(Arrow)?;
						let case_nil = self.parse_static()?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::Suc))?;
						let case_suc_parameters = (self.parse_identifier()?, self.parse_identifier()?);
						self.consume(Arrow)?;
						let case_suc = self.parse_static()?;
						self.consume(CurlyR)?;
						term = StaticPreterm::CaseNat {
							scrutinee: bx!(term),
							motive_parameter,
							motive: bx!(motive),
							case_nil: bx!(case_nil),
							case_suc_parameters,
							case_suc: bx!(case_suc),
						}
					}
				}
				_ => break,
			}
		}
		Some(term)
	}

	pub fn parse_dynamic_spine(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;
		let Lexeme { token, .. } = self.peek_lexeme()?;

		let mut term = if token == Keyword(self::Keyword::Suc) {
			self.next_lexeme();
			Suc(bx!(self.parse_dynamic_atom()?))
		} else {
			self.parse_dynamic_atom()?
		};

		while let Some(Lexeme { token, .. }) = self.peek_lexeme() {
			match token {
				_ if Self::is_dynamic_atom_start(token) => {
					term = Apply { scrutinee: bx!(term), argument: bx!(self.parse_dynamic_atom()?) };
				}
				Token::Project(projection) => {
					self.next_lexeme();
					term = DynamicPreterm::Project(bx!(term), projection);
				}
				TwoColon => {
					self.next_lexeme();
					if let Some(Keyword(self::Keyword::Bool)) = self.peek_lexeme().map(|x| x.token) {
						self.next_lexeme();
						self.consume(Pipe)?;
						let motive_parameter = self.parse_identifier()?;
						self.consume(Pipe)?;
						let motive = self.parse_dynamic()?;
						self.consume(CurlyL)?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::False))?;
						self.consume(Arrow)?;
						let case_false = self.parse_dynamic()?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::True))?;
						self.consume(Arrow)?;
						let case_true = self.parse_dynamic()?;
						self.consume(CurlyR)?;
						term = DynamicPreterm::CaseBool {
							scrutinee: bx!(term),
							motive: bind([motive_parameter], bx!(motive)),
							case_false: bx!(case_false),
							case_true: bx!(case_true),
						}
					} else {
						self.consume(Pipe)?;
						let motive_parameter = self.parse_identifier()?;
						self.consume(Pipe)?;
						let motive = self.parse_dynamic()?;
						self.consume(CurlyL)?;
						self.consume(Pipe)?;
						{
							let Lexeme { token: Number, range } = self.next_lexeme()? else {
								return None;
							};
							(&self.source[range.0..range.1] == "0").then_some(())? // TODO: Wrap this.
						}
						self.consume(Arrow)?;
						let case_nil = self.parse_dynamic()?;
						self.consume(Pipe)?;
						self.consume(Keyword(self::Keyword::Suc))?;
						let case_suc_parameters = (self.parse_identifier()?, self.parse_identifier()?);
						self.consume(Arrow)?;
						let case_suc = self.parse_dynamic()?;
						self.consume(CurlyR)?;
						term = DynamicPreterm::CaseNat {
							scrutinee: bx!(term),
							motive_parameter,
							motive: bx!(motive),
							case_nil: bx!(case_nil),
							case_suc_parameters,
							case_suc: bx!(case_suc),
						}
					}
				}
				_ => break,
			}
		}
		Some(term)
	}

	fn is_static_atom_start(token: Token) -> bool {
		use Token::*;

		use self::Keyword;
		matches!(
			token,
			Tick
				| SquareL | ParenL
				| Ast | Number
				| Keyword(
					Keyword::Nat
						| Keyword::Bool | Keyword::False
						| Keyword::True | Keyword::C0
						| Keyword::C1 | Keyword::Copy
				) | Identifier
		)
	}

	pub fn parse_static_atom(&mut self) -> Option<StaticPreterm> {
		use StaticPreterm::*;
		use Token::*;

		use self::Keyword;
		let Lexeme { token, range } = self.next_lexeme()?;
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
			Number => Num(self.source[range.0..range.1].parse().unwrap()),
			Keyword(Keyword::Nat) => Nat,
			Keyword(Keyword::Bool) => Bool,
			Keyword(Keyword::False) => BoolValue(false),
			Keyword(Keyword::True) => BoolValue(true),
			Keyword(Keyword::C0) => Copyability(self::Copyability::Trivial),
			Keyword(Keyword::C1) => Copyability(self::Copyability::Nontrivial),
			Keyword(Keyword::Copy) => CopyabilityType,
			Identifier => Variable(self.identifier(range)),
			_ => return None,
		};
		Some(term)
	}

	fn is_dynamic_atom_start(token: Token) -> bool {
		use Token::*;

		use self::Keyword;
		matches!(
			token,
			SquareL
				| ParenL | Ast
				| Number | Keyword(Keyword::Nat | Keyword::Bool | Keyword::False | Keyword::True)
				| Identifier
		)
	}

	fn parse_dynamic_atom(&mut self) -> Option<DynamicPreterm> {
		use DynamicPreterm::*;
		use Token::*;

		use self::Keyword;
		let Lexeme { token, range } = self.next_lexeme()?;
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
			Ast => {
				let copyability = self.parse_static_atom()?;
				DynamicPreterm::Universe { copyability: bx!(copyability) }
			}
			Number => Num(self.source[range.0..range.1].parse().unwrap()),
			Keyword(Keyword::Nat) => Nat,
			Keyword(Keyword::Bool) => Bool,
			Keyword(Keyword::False) => BoolValue(false),
			Keyword(Keyword::True) => BoolValue(true),
			Identifier => Variable(self.identifier(range)),
			_ => return None,
		};
		Some(term)
	}
}
