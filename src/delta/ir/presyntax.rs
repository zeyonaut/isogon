use crate::delta::common::{AnyBinder, Binder, Cpy, Field, Name, ReprAtom};

#[derive(Debug, Clone)]
pub struct Expression {
	pub range: (usize, usize),
	pub preterm: Preterm,
}

#[derive(Debug, Clone)]
pub enum Preterm {
	Variable(Name),

	Let { grade: usize, ty: Box<Expression>, argument: Box<Expression>, tail: Binder<Box<Expression>> },

	SwitchLevel(Box<Expression>),

	LetExp { grade: usize, grade_argument: usize, argument: Box<Expression>, tail: Binder<Box<Expression>> },

	Pi { grade: usize, base: Box<Expression>, family: Binder<Box<Expression>> },
	Lambda { grade: usize, body: Binder<Box<Expression>> },
	Call { callee: Box<Expression>, argument: Box<Expression> },

	Former(Former, Vec<Expression>),
	Constructor(Constructor, Vec<Expression>),
	Project(Box<Expression>, Projector),
	Split { scrutinee: Box<Expression>, motive: AnyBinder<Box<Expression>>, cases: Vec<(Pattern, Expression)> },
}

#[derive(Debug, Clone)]
pub enum Former {
	// Types and universe indices.
	Universe,
	Copy,
	Repr,

	// Quoted programs.
	Lift,

	// Repeated programs.
	Exp(usize),

	// Enumerated numbers.
	Enum(u16),

	// Paths.
	Id,

	// Wrappers.
	Bx,
	Wrap,
}

#[derive(Debug, Clone)]
pub enum Constructor {
	// Universe indices.
	Cpy(Cpy),
	CpyMax,

	ReprAtom(Option<ReprAtom>),
	ReprExp(usize),
	ReprPair,
	ReprMax,

	// Quoted programs.
	Exp(usize),

	// Enumerated numbers.
	Enum(u16, u8),

	// Paths.
	Refl,

	// Wrappers.
	Bx,
	Wrap,
}

#[derive(Debug, Clone)]
pub enum Projector {
	Bx,
	Wrap,
	Field(Field),
}

#[derive(Debug, Clone)]
pub enum Pattern {
	Variable(Option<Name>),
	// Inductive hypothesis witness.
	Witness { index: Option<Name>, witness: Option<Name> },
	Construction(Constructor, Vec<Pattern>),
}

impl Preterm {
	pub fn at(self, range: (usize, usize)) -> Expression { Expression { range, preterm: self } }
}
