use crate::common::{ArraySize, Field, Label, Level, Repr, ReprAtom, Symbol};

#[derive(Debug)]
pub struct Program {
	pub entry: Procedure,
	pub procedures: Vec<(Prototype, Procedure)>,
}

#[derive(Debug)]
pub struct Prototype {
	pub outer: Vec<(Label, Option<Layout>)>,
	pub parameter: (Label, Option<Layout>),
	pub result: Option<Layout>,
}

#[derive(Debug)]
pub struct Procedure {
	pub blocks: Vec<Block>,
}

#[derive(Debug)]
pub struct Block {
	pub parameters: Box<[(Symbol, Option<Layout>)]>,
	pub statements: Vec<Statement>,
	pub terminator: Option<Terminator>,
}

impl Block {
	pub fn new(parameters: Box<[(Symbol, Option<Layout>)]>) -> Self {
		Self { parameters, statements: Vec::new(), terminator: None }
	}
}

#[derive(Clone, Copy, Debug)]
#[repr(transparent)]
pub struct BlockId(pub usize);

#[derive(Clone)]
#[repr(transparent)]
pub struct Frame(pub usize);

impl Frame {
	pub fn and<T>(self, value: T) -> Framed<T> { Framed { frame: self, value } }

	pub fn id(&self) -> BlockId { BlockId(self.0) }
}

pub struct Framed<T> {
	pub frame: Frame,
	pub value: T,
}

impl<T> Framed<T> {
	pub fn unframe(self) -> (Frame, T) { (self.frame, self.value) }

	pub fn map<A>(self, f: impl FnOnce(T) -> A) -> Framed<A> {
		Framed { frame: self.frame, value: f(self.value) }
	}
}

impl From<&Repr> for Layout {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => match atom {
				ReprAtom::Byte => Self::Byte,
				ReprAtom::Nat => Self::Nat,
				ReprAtom::Ptr => Self::Ptr,
				ReprAtom::Fun => Self::Fun,
			},
			Repr::Pair(left, right) => Self::Pair([left.as_ref().into(), right.as_ref().into()].into()),
			Repr::Array(n, repr) => Self::Array(*n, Self::from(repr.as_ref()).into()),
		}
	}
}

#[derive(PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
pub enum Layout {
	Byte,
	Nat,
	Ptr,
	Fun,
	Pair(Box<[Self; 2]>),
	Array(ArraySize, Box<Self>),
}

#[derive(Debug)]
pub enum Terminator {
	Abort,
	Return(Value),
	Jump(BlockId, Box<[Value]>),
	Split(Value, Box<[BlockId]>),
	CaseNat {
		index: Value,
		limit: Value,
		body: BlockId,
		body_args: [Value; 2],
		exit: BlockId,
		exit_arg: Value,
	},
	Apply {
		procedure: Value,
		captures: Value,
		argument: Value,
		later: BlockId,
	},
}

#[derive(Debug)]
pub enum Statement {
	Assign(Symbol, Operation),
	Free(Load),
}

#[derive(Debug)]
pub enum Operation {
	Id(Value),
	Alloc(Value),
	Captures(Box<[Value]>),
	Suc(Load),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
	None,
	Num(usize),
	Enum(u16, u8),
	Procedure(usize),
	Load(Load),
	Function { procedure: Box<Self>, captures: Box<Self> },
	Array(Box<[Self]>),
	Pair(Box<Self>, Box<Self>),
	Wrap(Box<Self>),
}

impl Value {
	pub fn project(&self, projector: Projector) -> Self {
		match (&self, projector) {
			(Self::Load(load), projector) => load.project(projector).into(),
			(Self::Array(array), Projector::Exp(index, _)) => array[index].clone(),
			(Self::Function { procedure, captures: _ }, Projector::Procedure) => procedure.as_ref().clone(),
			(Self::Function { procedure: _, captures }, Projector::Captures) => captures.as_ref().clone(),
			(Self::Pair(basept, _), Projector::Field(Field::Base, _)) => basept.as_ref().clone(),
			(Self::Pair(_, fiberpt), Projector::Field(Field::Fiber, _)) => fiberpt.as_ref().clone(),
			(Self::Wrap(inner), Projector::Wrap(_)) => inner.as_ref().clone(),
			_ => unimplemented!(),
		}
	}

	pub fn function(procedure: impl Into<Self>, captures: impl Into<Self>) -> Self {
		Self::Function { procedure: Box::new(procedure.into()), captures: Box::new(captures.into()) }
	}

	pub fn pair(left: impl Into<Self>, right: impl Into<Self>) -> Self {
		Self::Pair(Box::new(left.into()), Box::new(right.into()))
	}
}

impl From<Load> for Value {
	fn from(value: Load) -> Self { Self::Load(value) }
}

impl From<Register> for Value {
	fn from(value: Register) -> Self { Self::Load(Load::reg(value)) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Load {
	pub register: Register,
	pub projectors: Vec<Projector>,
}

impl Load {
	pub fn reg(register: Register) -> Self { Self { register, projectors: vec![] } }
	pub fn project(&self, projector: Projector) -> Self {
		let mut load = self.clone();
		load.projectors.push(projector);
		load
	}
}

impl From<Register> for Load {
	fn from(value: Register) -> Self { Self::reg(value) }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Projector {
	Exp(usize, Option<Layout>),
	Procedure,
	Captures,
	Field(Field, [Option<Layout>; 2]),
	Bx(Option<Layout>),
	Wrap(Option<Layout>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Register {
	Outer(Level),
	Parameter,
	Local(Symbol),
}
