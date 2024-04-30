use crate::common::Field;

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Token {
	Whitespace,
	Keyword(Keyword),
	Pragma(Pragma),
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
pub enum Pragma {
	Fragment,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Keyword {
	Def,
	Let,

	Copy,
	C0,
	C1,
	CMax,

	Repr,
	RPtr,
	RByte,
	RNat,
	RFun,
	RPair,
	RMax,
	RExp,
	RNone,

	ExpProject,

	// Wrappers.
	Bx,
	BxValue,
	BxProject,
	Wrap,
	WrapValue,
	WrapProject,

	Bool,
	True,
	False,

	Id,
	Refl,
	Cast,

	Nat,
	Suc,
}

pub struct TokenizedSource<'a> {
	pub source: &'a str,
	pub tokens: Box<[Token]>,
	pub ranges: Box<[(usize, usize)]>,
}
