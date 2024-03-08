use crate::gamma::common::{Copyability, Field, Name, ReprAtom};

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

	Let {
		assignee: Option<Name>,
		is_crisp: bool,
		ty: Box<Expression>,
		argument: Box<Expression>,
		tail: Box<Expression>,
	},

	Pi {
		parameter: Option<Name>,
		base: Box<Expression>,
		family: Box<Expression>,
	},
	Sigma {
		parameter: Option<Name>,
		base: Box<Expression>,
		family: Box<Expression>,
	},
	Lambda {
		parameter: Option<Name>,
		body: Box<Expression>,
	},
	Pair {
		basepoint: Box<Expression>,
		fiberpoint: Box<Expression>,
	},

	Former(Former, Vec<Expression>),
	Constructor(Constructor, Vec<Expression>),

	Project(Box<Expression>, Projector),
	Call {
		callee: Box<Expression>,
		argument: Box<Expression>,
	},
	Split {
		scrutinee: Box<Expression>,
		motive_parameter: Vec<Option<Name>>,
		motive: Box<Expression>,
		cases: Vec<(Pattern, Expression)>,
	},
}

#[derive(Debug, Clone)]
pub enum Former {
	Lift,
	Rc,
	Wrap,
	Nat,
	Enum(u16),
	Id,
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

	EnumValue(u16, u8),

	Refl,

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

impl Preterm {
	pub fn at(self, range: (usize, usize)) -> Expression {
		Expression { range, preterm: self }
	}
}
