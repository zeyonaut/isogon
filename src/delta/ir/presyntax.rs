use crate::delta::common::{AnyBinder, Binder, Copyability, Field, Name, ReprAtom};

#[derive(Debug, Clone)]
pub struct Expression {
	pub range: (usize, usize),
	pub preterm: Preterm,
}

#[derive(Debug, Clone)]
pub enum Preterm {
	Variable(Name),

	Quote(Box<Expression>),
	Splice(Box<Expression>),

	Let { grade: Option<usize>, ty: Box<Expression>, argument: Box<Expression>, tail: Binder<Box<Expression>> },

	Pi { grade: Option<usize>, base: Box<Expression>, family: Binder<Box<Expression>> },
	Lambda { grade: Option<usize>, body: Binder<Box<Expression>> },

	Former(Former, Vec<Expression>),
	Constructor(Constructor, Vec<Expression>),

	Call { callee: Box<Expression>, argument: Box<Expression> },
}

#[derive(Debug, Clone)]
pub enum Former {
	Poly(usize),
	Lift,
	Copy,
	Repr,
	Universe,
}

#[derive(Debug, Clone)]
pub enum Constructor {
	Poly(usize),

	Copyability(Copyability),
	CopyMax,

	ReprAtom(Option<ReprAtom>),
	ReprPair,
	ReprMax,
	ReprUniv,
}

impl Preterm {
	pub fn at(self, range: (usize, usize)) -> Expression { Expression { range, preterm: self } }
}
