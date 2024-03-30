use crate::delta::common::{AnyBinder, Binder, Copyability, Field, Name, ReprAtom};

#[derive(Debug, Clone)]
pub struct Expression {
	pub range: (usize, usize),
	pub preterm: Preterm,
}

#[derive(Debug, Clone)]
pub enum Preterm {
	Variable(Name),

	SwitchLevel(Box<Expression>),

	Let { grade: usize, ty: Box<Expression>, argument: Box<Expression>, tail: Binder<Box<Expression>> },
	LetExp { grade: usize, grade_argument: usize, argument: Box<Expression>, tail: Binder<Box<Expression>> },

	Pi { grade: usize, base: Box<Expression>, family: Binder<Box<Expression>> },
	Lambda { grade: usize, body: Binder<Box<Expression>> },

	Former(Former, Vec<Expression>),
	Constructor(Constructor, Vec<Expression>),

	Call { callee: Box<Expression>, argument: Box<Expression> },
}

#[derive(Debug, Clone)]
pub enum Former {
	Exp(usize),
	Lift,
	Copy,
	Repr,
	Universe,
}

#[derive(Debug, Clone)]
pub enum Constructor {
	Exp(usize),

	Copyability(Copyability),
	CopyMax,

	ReprAtom(Option<ReprAtom>),
	ReprExp(usize),
	ReprPair,
	ReprMax,
	ReprUniv,
}

impl Preterm {
	pub fn at(self, range: (usize, usize)) -> Expression { Expression { range, preterm: self } }
}
