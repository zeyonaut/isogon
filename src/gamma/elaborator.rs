use super::common::Index;

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Index),
	Lambda { parameter: String, body: Box<Self> },
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	Pi { parameter: String, base: Box<Self>, family: Box<Self> },
	Let { assignee: String, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Universe,
	Splice(Box<StaticTerm>),
}
