use crate::gamma::common::{Copyability, Field, Name, ReprAtom};

#[derive(Debug, Clone)]
pub enum Preterm {
	Variable(Name),

	Quote(Box<Self>),
	Splice(Box<Self>),

	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },

	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Lambda { parameter: Name, body: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },

	Former(Former, Vec<Self>),
	Constructor(Constructor, Vec<Self>),

	Project(Box<Self>, Projector),
	Call { callee: Box<Self>, argument: Box<Self> },
	Split { scrutinee: Box<Self>, motive_parameter: Name, motive: Box<Self>, cases: Vec<(Pattern, Self)> },
}

#[derive(Debug, Clone)]
pub enum Former {
	Lift,
	Rc,
	Wrap,
	Nat,
	Bool,
	Copy,
	Repr,
	Universe,
}

#[derive(Debug, Clone)]
pub enum Constructor {
	Rc,

	Wrap,

	Num(usize),
	Suc,

	BoolValue(bool),

	Copyability(Copyability),
	CopyMax,

	ReprAtom(Option<ReprAtom>),
	ReprPair,
	ReprMax,
	ReprUniv,
}

#[derive(Debug, Clone)]
pub enum Projector {
	Rc,
	Wrap,
	Field(Field),
}

#[derive(Debug, Clone)]
pub enum Pattern {
	Variable(Name),
	// Inductive hypothesis witness.
	Witness { index: Name, witness: Name },
	Construction(Constructor, Vec<Pattern>),
}
