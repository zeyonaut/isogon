use crate::common::{AnyBinder, Binder, Cost, Cpy, Field, Fragment, Index, Label, Name, ReprAtom};

#[derive(Debug, Clone)]
pub struct ParsedProgram {
	pub fragment: Fragment,
	pub expr: Expression,
}

#[derive(Debug, Clone)]
pub struct Expression {
	pub range: (usize, usize),
	pub preterm: ParsedPreterm,
}

#[derive(Debug, Clone, Copy)]
pub struct ParsedLabel {
	pub locus: usize,
	pub label: Label,
}

#[derive(Debug, Clone)]
pub struct ParsedPreterm(pub Preterm<ParsedLabel, Expression>);

pub struct PurePreterm(pub Preterm<Label, Self>);

#[derive(Debug, Clone)]
pub enum Preterm<L, E> {
	Variable(Name),
	Index(Index),

	Let { is_meta: bool, grade: Option<Cost>, ty: Box<E>, argument: Box<E>, tail: Binder<L, Box<E>> },

	SwitchLevel(Box<E>),

	ExpLet { grade: Option<Cost>, grade_argument: Cost, argument: Box<E>, tail: Binder<L, Box<E>> },

	Pi { fragment: Fragment, base: Box<E>, family: Binder<L, Box<E>> },
	Lambda { body: Binder<L, Box<E>> },
	Call { callee: Box<E>, argument: Box<E> },

	Sg { base: Box<E>, family: Binder<L, Box<E>> },
	Pair { basepoint: Box<E>, fiberpoint: Box<E> },
	SgLet { grade: usize, argument: Box<E>, tail: Binder<L, Box<E>, 2> },

	Former(Former, Vec<E>),
	Constructor(Constructor, Vec<E>),
	Project(Box<E>, Projector),
	Split { scrutinee: Box<E>, is_cast: bool, motive: AnyBinder<L, Box<E>>, cases: Vec<(Pattern<L>, E)> },
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
	Exp(Cost),

	// Enumerated numbers.
	Enum(u16),

	// Paths.
	Id,

	// Natural numbers.
	Nat,

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
	Exp(Cost),

	// Enumerated numbers.
	Enum(u16, u8),

	// Paths.
	Refl,

	// Natural numbers.
	Num(usize),
	Suc,

	// Wrappers.
	Bx,
	Wrap,
}

#[derive(Debug, Clone)]
pub enum Projector {
	Exp,
	Bx,
	Wrap,
	Field(Field),
}

#[derive(Debug, Clone)]
pub enum Pattern<L> {
	Variable(L),
	// Inductive hypothesis witness.
	Witness { index: L, witness: L },
	Construction(Constructor, Vec<Self>),
}

impl Preterm<ParsedLabel, Expression> {
	pub fn at(self, range: (usize, usize)) -> Expression { Expression { range, preterm: ParsedPreterm(self) } }
}
