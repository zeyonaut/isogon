use crate::common::{ArraySize, Field, Label, Level, Repr, ReprAtom, Symbol};

#[derive(Debug)]
pub struct Program {
	pub entry_prototype: Prototype,
	pub entry: Procedure,
	pub procedures: Vec<(Prototype, Procedure)>,
}

#[derive(Debug, Clone)]
pub struct Prototype {
	pub outer: Option<Vec<(Label, Option<Layout>)>>,
	pub parameter: Option<(Label, Option<Layout>)>,
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

impl Layout {
	pub fn pair(layouts: [Option<Self>; 2]) -> Option<Self> {
		let [a, b] = layouts;
		let Some(a) = a else { return b };
		let Some(b) = b else { return Some(a) };
		Some(Self::Pair([a, b].into()))
	}
}

#[derive(Debug)]
pub enum Terminator {
	Abort,
	Return(Value),
	Jump(BlockId, Box<[Value]>),
	Split(Value, Box<[BlockId]>),
	CaseNat { index: Value, limit: Value, body: BlockId, exit: BlockId },
}

#[derive(Debug)]
pub enum Statement {
	Assign(Symbol, Value),
	Alloc(Symbol, Value),
	Captures(Symbol, Box<[Value]>),
	Free(Load),
	Call { symbol: Symbol, result_repr: Option<Layout>, procedure: Value, captures: Value, argument: Value },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Value {
	None,
	Num(u64),
	Add(Box<Self>, u64),
	Enum(u16, u8),
	Procedure(usize),
	Load(Load),
	Function { procedure: Box<Self>, captures: Box<Self> },
	Array(Box<[Self]>),
	Pair(Box<Self>, Box<Self>),
}

impl Value {
	pub fn project(&self, projector: Projector) -> Self {
		match (&self, projector) {
			(Self::Load(load), projector) => load.project(projector).into(),
			(Self::Array(array), Projector::Exp(index, _)) => array[index as usize].clone(),
			(Self::Function { procedure, captures: _ }, Projector::Procedure) => procedure.as_ref().clone(),
			(Self::Function { procedure: _, captures }, Projector::Environment) => captures.as_ref().clone(),
			(Self::Pair(basept, _), Projector::Field(Field::Base, _)) => basept.as_ref().clone(),
			(Self::Pair(_, fiberpt), Projector::Field(Field::Fiber, _)) => fiberpt.as_ref().clone(),
			_ => unimplemented!(),
		}
	}

	pub fn function(procedure: impl Into<Self>, captures: impl Into<Self>) -> Self {
		Self::Function { procedure: Box::new(procedure.into()), captures: Box::new(captures.into()) }
	}

	pub fn pair(left: impl Into<Self>, right: impl Into<Self>) -> Self {
		Self::Pair(Box::new(left.into()), Box::new(right.into()))
	}

	pub fn suc(self) -> Self {
		match self {
			Self::Num(n) => Self::Num(n.checked_add(1).unwrap()),
			Self::Add(a, b) => Self::Add(a, b.checked_add(1).unwrap()),
			Self::Load(a) => Self::Add(Box::new(a.into()), 1),
			_ => panic!(),
		}
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
	Exp(u64, Option<Layout>),
	Procedure,
	Environment,
	Field(Field, [Option<Layout>; 2]),
	Bx(Option<Layout>),
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Register {
	Outer(Level),
	Parameter,
	Local(Symbol),
}

pub fn pretty_print_linear(f: &mut impl std::fmt::Write, program: &Program) -> std::fmt::Result {
	write!(f, "entry : ")?;
	print_prototype(f, &program.entry_prototype)?;
	writeln!(f, " {{")?;
	print_procedure(f, &program.entry)?;
	writeln!(f, "}}")?;
	writeln!(f)?;

	for (i, (prototype, procedure)) in program.procedures.iter().enumerate() {
		write!(f, "proc_{i} : ")?;
		print_prototype(f, prototype)?;
		writeln!(f, " {{")?;
		print_procedure(f, procedure)?;
		writeln!(f, "}}")?;
		writeln!(f)?;
	}

	Ok(())
}

fn print_procedure(f: &mut impl std::fmt::Write, procedure: &Procedure) -> std::fmt::Result {
	for (i, block) in procedure.blocks.iter().enumerate() {
		write!(f, "    block{i}")?;
		if !block.parameters.is_empty() {
			write!(f, "(")?;
			// TODO: Maybe also print layouts?
			if let Some(n) = block.parameters.len().checked_sub(1) {
				for (x, layout) in block.parameters.iter().take(n) {
					write!(f, "v{} : ", x.0)?;
					print_opt_layout(f, layout)?;
					write!(f, ", ")?;
				}
			}
			if let Some((x, layout)) = block.parameters.last() {
				write!(f, "v{} : ", x.0)?;
				print_opt_layout(f, layout)?;
			}
			write!(f, ")")?;
		}
		writeln!(f, ":")?;

		for statement in &block.statements {
			write!(f, "    ")?;
			print_statement(f, statement)?;
			writeln!(f)?;
		}
		write!(f, "    ")?;
		print_terminator(f, block.terminator.as_ref().unwrap())?;
		writeln!(f)?;
		if i + 1 < procedure.blocks.len() {
			writeln!(f)?;
		}
	}

	Ok(())
}

fn print_terminator(f: &mut impl std::fmt::Write, terminator: &Terminator) -> std::fmt::Result {
	match terminator {
		Terminator::Abort => write!(f, "abort")?,
		Terminator::Return(value) => {
			write!(f, "return ")?;
			print_value(f, value)?;
		}
		Terminator::Jump(id, values) => {
			write!(f, "jump block{}(", id.0)?;
			print_values(f, values)?;
			write!(f, ")")?;
		}
		Terminator::Split(value, blocks) => {
			write!(f, "split ")?;
			print_value(f, value)?;
			write!(f, " into (")?;
			if let Some(n) = blocks.len().checked_sub(1) {
				for x in blocks.iter().take(n) {
					write!(f, "block{}, ", x.0)?;
				}
			}
			if let Some(block) = blocks.last() {
				write!(f, "block{}", block.0)?;
			}
			write!(f, ")")?;
		}
		Terminator::CaseNat { index, limit, body, exit } => {
			write!(f, "if ")?;
			print_value(f, index)?;
			write!(f, " < ")?;
			print_value(f, limit)?;
			write!(f, " then ")?;
			write!(f, "block{}()", body.0)?;
			write!(f, " else ")?;
			write!(f, "block{}()", exit.0)?;
		}
	}
	Ok(())
}

fn print_statement(f: &mut impl std::fmt::Write, statement: &Statement) -> std::fmt::Result {
	match statement {
		Statement::Assign(symbol, value) => {
			write!(f, "v{} = ", symbol.0)?;
			print_value(f, value)?;
		}
		Statement::Alloc(symbol, value) => {
			write!(f, "v{} = alloc ", symbol.0)?;
			print_value(f, value)?;
		}
		Statement::Captures(symbol, values) => {
			write!(f, "v{} = env (", symbol.0)?;
			print_values(f, values)?;
			write!(f, ")")?;
		}
		Statement::Free(load) => {
			write!(f, "free ")?;
			print_load(f, load)?;
		}
		Statement::Call { symbol, result_repr: _, procedure, captures, argument } => {
			write!(f, "v{} = call ", symbol.0)?;
			print_value(f, procedure)?;
			write!(f, " in ")?;
			print_value(f, captures)?;
			write!(f, " with ")?;
			print_value(f, argument)?;
		}
	}
	Ok(())
}

fn print_values(f: &mut impl std::fmt::Write, values: &[Value]) -> std::fmt::Result {
	if let Some(n) = values.len().checked_sub(1) {
		for x in values.iter().take(n) {
			print_value(f, x)?;
			write!(f, ", ")?;
		}
	}
	if let Some(value) = values.last() {
		print_value(f, value)?;
	}
	Ok(())
}

fn print_value(f: &mut impl std::fmt::Write, value: &Value) -> std::fmt::Result {
	match value {
		Value::None => write!(f, "none")?,
		Value::Num(n) => write!(f, "{n}")?,
		Value::Add(a, b) => {
			print_value(f, a)?;
			write!(f, " + {b}")?;
		}
		Value::Enum(k, n) => write!(f, "{n}_{k}")?,
		Value::Procedure(n) => write!(f, "proc_{n}")?,
		Value::Load(load) => print_load(f, load)?,
		Value::Function { procedure, captures } => {
			write!(f, "fun (")?;
			print_value(f, procedure)?;
			write!(f, ", ")?;
			print_value(f, captures)?;
			write!(f, ")")?;
		}
		Value::Array(a) => {
			write!(f, "[")?;
			print_values(f, a)?;
			write!(f, "]")?;
		}
		Value::Pair(a, b) => {
			write!(f, "(")?;
			print_value(f, a)?;
			write!(f, ", ")?;
			print_value(f, b)?;
			write!(f, ")")?;
		}
	}
	Ok(())
}

fn print_load(f: &mut impl std::fmt::Write, load: &Load) -> std::fmt::Result {
	match load.register {
		Register::Outer(n) => write!(f, "env.{}", n.0)?,
		Register::Parameter => write!(f, "param")?,
		Register::Local(n) => write!(f, "v{}", n.0)?,
	}
	for projector in &load.projectors {
		match projector {
			Projector::Exp(n, _) => write!(f, ".{n}")?,
			Projector::Procedure => write!(f, ".proc")?,
			Projector::Environment => write!(f, ".env")?,
			Projector::Field(Field::Base, _) => write!(f, ".0")?,
			Projector::Field(Field::Fiber, _) => write!(f, ".1")?,
			Projector::Bx(_) => write!(f, ".deref")?,
		}
	}
	Ok(())
}

pub fn print_opt_layout(f: &mut impl std::fmt::Write, layout: &Option<Layout>) -> std::fmt::Result {
	if let Some(layout) = &layout {
		print_layout(f, layout)?;
	} else {
		writeln!(f, "()")?;
	}
	Ok(())
}

pub fn print_layout(f: &mut impl std::fmt::Write, layout: &Layout) -> std::fmt::Result {
	match layout {
		Layout::Byte => write!(f, "u8")?,
		Layout::Nat => write!(f, "nat")?,
		Layout::Ptr => write!(f, "ptr")?,
		Layout::Fun => write!(f, "fun")?,
		Layout::Pair(pair) => {
			let [a, b] = pair.each_ref();
			write!(f, "(")?;
			print_layout(f, a)?;
			write!(f, ", ")?;
			print_layout(f, b)?;
			write!(f, ")")?;
		}
		Layout::Array(n, l) => {
			write!(f, "[")?;
			print_layout(f, l)?;
			write!(f, "; {}]", n.0)?;
		}
	}
	Ok(())
}

fn print_layouts(f: &mut impl std::fmt::Write, layouts: &[Option<Layout>]) -> std::fmt::Result {
	if let Some(n) = layouts.len().checked_sub(1) {
		for x in layouts.iter().take(n) {
			print_opt_layout(f, x)?;
			write!(f, ", ")?;
		}
	}
	if let Some(value) = layouts.last() {
		print_opt_layout(f, value)?;
	}
	Ok(())
}

fn print_prototype(f: &mut impl std::fmt::Write, prototype: &Prototype) -> std::fmt::Result {
	if let Some(outer) = &prototype.outer {
		let layouts = outer.iter().map(|(_, l)| l.clone()).collect::<Vec<_>>();
		write!(f, "[")?;
		print_layouts(f, &layouts)?;
		write!(f, "]")?;
	}
	write!(f, "(")?;
	if let Some((_, parameter)) = &prototype.parameter {
		print_opt_layout(f, parameter)?;
	}
	write!(f, ") -> ")?;
	print_opt_layout(f, &prototype.result)?;
	Ok(())
}
