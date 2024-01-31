use std::{collections::HashMap, hash::Hash};

use lasso::Rodeo;

use super::closed::Term;
use crate::gamma::common::{Copyability, Level, Name, Projection, Repr, ReprAtom, UniverseKind};

pub struct Program {
	pub entry: Procedure,
	pub procedures: Vec<(Prototype, Procedure)>,
}

pub struct Prototype {
	// TODO: I think these all need to be converted into block and operands too, but I'm not sure in what way.
	// Perhaps as a chain of blocks prepended to the entry block, with the operands available for drops later?
	pub outer: Vec<(Name, Term)>,
	pub parameter: (Name, Term),
}

pub struct Procedure {
	pub entry_label: Symbol,
	pub blocks: HashMap<Symbol, Block>,
}

pub struct Block {
	pub parameters: Vec<Symbol>,
	pub statements: Vec<Statement>,
	pub terminator: Terminator,
}

pub enum Terminator {
	Branch {
		operand: Operand,
		false_block: Symbol,
		false_operands: Vec<Operand>,
		true_block: Symbol,
		true_operands: Vec<Operand>,
	},
	Jump {
		block: Option<Symbol>,
		operand: Operand,
	},
	Apply {
		callee: Operand,
		argument: Operand,
		return_block: Symbol,
	},
}

pub enum Statement {
	Assign(Symbol, Operation),
}

pub enum Operation {
	Function { captures: Vec<Operand>, procedure_index: usize },
	Pi { base: Operand, family: Operand },
	Sigma { base: Operand, family: Operand },
	Id(Operand),
	Pair { basepoint: Operand, fiberpoint: Operand },
	Suc(Operand),
	WrapType(Operand),
	WrapNew(Operand),
	RcType(Operand),
	RcNew(Operand),
	IsPositive(Operand),
	Pred(Operand),
}

#[derive(Clone)]
pub enum Literal {
	Nat,
	Bool,
	Universe(UniverseKind),
	Num(usize),
	BoolValue(bool),
}

#[derive(Clone)]
pub enum Operand {
	Literal(Literal),
	Load(Load),
}

impl Operand {
	pub fn modify(self, modifier: Modifier) -> Self {
		match self {
			// TODO: Should we allow arbitrarily complex literals at this stage?
			Operand::Literal(_literal) => unimplemented!(),
			Operand::Load(load) => Operand::Load(load.modify(modifier)),
		}
	}
}

#[derive(Clone)]
pub struct Load {
	pub register: Register,
	pub modifiers: Vec<Modifier>,
}

impl Load {
	pub fn reg(register: Register) -> Self {
		Self { register, modifiers: vec![] }
	}
	pub fn modify(mut self, modifier: Modifier) -> Self {
		self.modifiers.push(modifier);
		self
	}
}

#[derive(Clone)]
pub enum Modifier {
	Projection(Projection),
	UnRc,
	Unwrap,
}

#[derive(Clone)]
pub enum Register {
	Outer(Level),
	Parameter,
	Local(Symbol),
}

pub struct SymbolGenerator(usize);

impl SymbolGenerator {
	pub fn new() -> Self {
		Self(0)
	}

	pub fn generate(&mut self) -> Symbol {
		let symbol = self.0;
		self.0 += 1;
		Symbol(symbol)
	}
}

#[repr(transparent)]
#[derive(PartialEq, Eq, Hash, Clone, Copy)]
pub struct Symbol(pub usize);

// Pretty printers.
impl Program {
	pub fn pretty(&self, interner: &Rodeo) {
		println!("entry:");
		self.entry.pretty(interner);
		println!();
		for (i, (prototype, procedure)) in self.procedures.iter().enumerate() {
			prototype.pretty(i, interner);
			procedure.pretty(interner);
			println!();
		}
	}
}

impl Prototype {
	pub fn pretty(&self, i: usize, interner: &Rodeo) {
		print!("proc_{i}[");
		for (out, _) in &self.outer {
			print!("{}, ", interner.resolve(out))
		}
		println!("]({}):", interner.resolve(&self.parameter.0));
	}
}

impl Procedure {
	pub fn pretty(&self, interner: &Rodeo) {
		println!("    entry => block_{}", self.entry_label.0);
		for (id, block) in self.blocks.iter() {
			print!("    block_{}(", id.0);
			for p in &block.parameters {
				print!("{}, ", p.0);
			}
			println!("):");

			for statement in &block.statements {
				statement.pretty(interner);
			}

			block.terminator.pretty(interner);
		}
	}
}

impl Statement {
	pub fn pretty(&self, interner: &Rodeo) {
		print!("        ");
		match self {
			Statement::Assign(a, b) => {
				print!("{} := ", a.0);
				b.pretty(interner);
				println!();
			}
		}
	}
}

impl Operation {
	pub fn pretty(&self, interner: &Rodeo) {
		match self {
			Operation::Function { captures, procedure_index } => {
				print!("proc_{} {{", procedure_index);

				for o in captures {
					o.pretty(interner);
					print!(", ");
				}
				print!("}}")
			}
			Operation::Pi { base, family } => {
				print!("pi {{");
				base.pretty(interner);
				print!(", ");
				family.pretty(interner);
				print!("}}");
			}
			Operation::Sigma { base, family } => {
				print!("sigma {{");
				base.pretty(interner);
				print!(", ");
				family.pretty(interner);
				print!("}}");
			}
			Operation::Id(a) => a.pretty(interner),
			Operation::Pair { basepoint, fiberpoint } => {
				print!("(");
				basepoint.pretty(interner);
				print!(", ");
				fiberpoint.pretty(interner);
				print!(")");
			}
			Operation::Suc(o) => pretty_unary_operation("suc", o, interner),
			Operation::WrapType(o) => pretty_unary_operation("Wrap", o, interner),
			Operation::WrapNew(o) => pretty_unary_operation("wrap", o, interner),
			Operation::RcType(o) => pretty_unary_operation("RC", o, interner),
			Operation::RcNew(o) => pretty_unary_operation("rc", o, interner),
			Operation::IsPositive(o) => pretty_unary_operation("is_positive", o, interner),
			Operation::Pred(o) => pretty_unary_operation("pred", o, interner),
		}
	}
}

fn pretty_unary_operation(op: &'static str, operand: &Operand, interner: &Rodeo) {
	print!("{} {{", op);
	operand.pretty(interner);
	print!("}}");
}

impl Terminator {
	pub fn pretty(&self, interner: &Rodeo) {
		print!("        ");
		match self {
			Terminator::Branch { operand, false_block, false_operands, true_block, true_operands } => {
				print!("branch (");
				operand.pretty(interner);
				print!(") block_{}(", false_block.0);
				for o in false_operands {
					o.pretty(interner);
					print!(", ");
				}
				print!(") block_{}(", true_block.0);
				for o in true_operands {
					o.pretty(interner);
					print!(", ");
				}
				println!(")");
			}
			Terminator::Jump { block, operand } => {
				print!("jump ");
				if let Some(b) = block {
					print!("block_{} ", b.0);
				} else {
					print!("ret ");
				}
				operand.pretty(interner);
				println!();
			}
			Terminator::Apply { callee, argument, return_block } => {
				print!("call ");
				callee.pretty(interner);
				print!(" with ");
				argument.pretty(interner);
				println!(" => block_{}", return_block.0);
			}
		}
	}
}

impl Operand {
	pub fn pretty(&self, _interner: &Rodeo) {
		match self {
			Operand::Literal(v) => match v {
				Literal::Nat => print!("nat"),
				Literal::Bool => print!("bool"),
				Literal::Universe(UniverseKind(c, r)) => {
					print!("@type(");
					match c {
						Copyability::Trivial => print!("c0"),
						Copyability::Nontrivial => print!("c1"),
					}
					print!(", ");
					if let Some(repr) = r.as_ref() {
						repr.pretty();
					} else {
						print!("rnone");
					}
					print!(")")
				}
				Literal::Num(n) => print!("{n}"),
				Literal::BoolValue(b) => print!("{b}"),
			},
			Operand::Load(m) => {
				match m.register {
					Register::Outer(n) => print!("@outer({})", n.0),
					Register::Parameter => print!("@parameter"),
					Register::Local(n) => print!("@local({})", n.0),
				}

				for x in &m.modifiers {
					match x {
						Modifier::Projection(Projection::Base) => print!("/."),
						Modifier::Projection(Projection::Fiber) => print!("/!"),
						Modifier::UnRc => print!("/unrc"),
						Modifier::Unwrap => print!("/unwrap"),
					}
				}
			}
		}
	}
}

impl Repr {
	fn pretty(&self) {
		match self {
			Repr::Atom(atom) => match atom {
				ReprAtom::Class => print!("rclass"),
				ReprAtom::Pointer => print!("rpointer"),
				ReprAtom::Byte => print!("rbyte"),
				ReprAtom::Nat => print!("rnat"),
				ReprAtom::Fun => print!("rfun"),
			},
			Repr::Pair(a, b) => {
				print!("@rpair(");
				a.pretty();
				print!(", ");
				b.pretty();
				print!(")");
			}
			Repr::Max(a, b) => {
				print!("@rmax(");
				a.pretty();
				print!(", ");
				b.pretty();
				print!(")");
			}
		}
	}
}
