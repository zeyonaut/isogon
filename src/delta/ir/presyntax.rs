use crate::delta::common::{AnyBinder, Binder, Cost, Cpy, Field, Name, ReprAtom};

#[derive(Debug, Clone)]
pub struct ParsedProgram {
	pub fragment: u8,
	pub expr: Expression,
}

#[derive(Debug, Clone)]
pub struct Expression {
	pub range: (usize, usize),
	pub preterm: ParsedPreterm,
}

#[derive(Debug, Clone)]
pub struct ParsedPreterm(pub Preterm<Expression>);

pub struct PurePreterm(pub Preterm<Self>);

#[derive(Debug, Clone)]
pub enum Preterm<E> {
	Variable(Name),

	Let { is_meta: bool, grade: Option<Cost>, ty: Box<E>, argument: Box<E>, tail: Binder<Box<E>> },

	SwitchLevel(Box<E>),

	LetExp { grade: usize, grade_argument: usize, argument: Box<E>, tail: Binder<Box<E>> },

	Pi { grade: usize, base: Box<E>, family: Binder<Box<E>> },
	Lambda { grade: usize, body: Binder<Box<E>> },
	Call { callee: Box<E>, argument: Box<E> },

	Sg { base: Box<E>, family: Binder<Box<E>> },
	Pair { basepoint: Box<E>, fiberpoint: Box<E> },
	SgLet { grade: usize, argument: Box<E>, tail: Binder<Box<E>, 2> },

	Former(Former, Vec<E>),
	Constructor(Constructor, Vec<E>),
	Project(Box<E>, Projector),
	Split { scrutinee: Box<E>, is_cast: bool, motive: AnyBinder<Box<E>>, cases: Vec<(Pattern, E)> },
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
	Exp(usize),

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

impl Preterm<Expression> {
	pub fn at(self, range: (usize, usize)) -> Expression { Expression { range, preterm: ParsedPreterm(self) } }
}
