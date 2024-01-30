use std::{collections::HashMap, hash::Hash};

use lasso::{Interner, Rodeo};

use super::{
	closer::{ClosedValue, Function, Variable},
	common::{Binder, Copyability, Level, Name, Projection, Repr, ReprAtom, UniverseKind},
};

struct ProcedureBuilder {
	symbol_generator: SymbolGenerator,
	level_to_operand: Vec<Operand>,
	blocks: HashMap<Symbol, Block>,
}

pub struct Program {
	entry: Procedure,
	procedures: Vec<(Prototype, Procedure)>,
}

pub struct Prototype {
	// TODO: I think these all need to be converted into block and operands too, but I'm not sure in what way.
	// Perhaps as a chain of blocks prepended to the entry block, with the operands available for drops later?
	outer: Vec<(Name, ClosedValue)>,
	parameter: (Name, ClosedValue),
}

pub struct Procedure {
	entry_label: Symbol,
	blocks: HashMap<Symbol, Block>,
}

struct Preblock {
	label: Symbol,
	parameters: Vec<Symbol>,
	statements: Vec<Statement>,
}

struct Block {
	parameters: Vec<Symbol>,
	statements: Vec<Statement>,
	terminator: Terminator,
}

enum Terminator {
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

enum Statement {
	Assign(Symbol, Operation),
}

enum Operation {
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
enum Literal {
	Nat,
	Bool,
	Universe(UniverseKind),
	Num(usize),
	BoolValue(bool),
}

#[derive(Clone)]
enum Operand {
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
struct Load {
	register: Register,
	modifiers: Vec<Modifier>,
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
enum Modifier {
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
	pub fn pretty(&self, interner: &Rodeo) {
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
				ReprAtom::Pointer =>  print!("rpointer"),
				ReprAtom::Byte =>  print!("rbyte"),
				ReprAtom::Nat =>  print!("rnat"),
				ReprAtom::Fun =>  print!("rfun"),
			},
			Repr::Pair(a, b) => {
				print!("@rpair(");
				a.pretty();
				print!(", ");
				b.pretty();
				print!(")");
			},
			Repr::Max(a, b) => {
				print!("@rmax(");
				a.pretty();
				print!(", ");
				b.pretty();
				print!(")");
			},
		}
	}
}

pub fn sequentialize(program: super::closer::Program) -> Program {
	let entry = build_procedure(program.entry);

	let procedures = program
		.procedures
		.into_iter()
		.map(|procedure| {
			(
				Prototype { outer: procedure.captured_parameters, parameter: procedure.parameter },
				build_procedure(procedure.body),
			)
		})
		.collect::<Vec<_>>();

	Program { entry, procedures }
}

fn build_procedure(value: ClosedValue) -> Procedure {
	let mut builder = ProcedureBuilder::new();

	let entry_label = builder.symbol_generator.generate();
	let mut preblock = Preblock { label: entry_label, parameters: vec![], statements: vec![] };

	let operand = builder.generate(&mut preblock, value);

	builder.terminate(preblock, Terminator::Jump { block: None, operand });

	Procedure { entry_label, blocks: builder.blocks }
}

impl ProcedureBuilder {
	fn new() -> Self {
		Self { symbol_generator: SymbolGenerator::new(), level_to_operand: vec![], blocks: HashMap::new() }
	}

	pub fn push_block(&mut self, block: Block) -> Symbol {
		let label = self.symbol_generator.generate();
		self.blocks.insert(label, block);
		label
	}

	pub fn terminate(&mut self, Preblock { label, parameters, statements }: Preblock, terminator: Terminator) {
		self.blocks.insert(label, Block { parameters, statements, terminator });
	}

	pub fn generate_with<const N: usize>(
		&mut self,
		preblock: &mut Preblock,
		binder: Binder<Box<ClosedValue>, N>,
		operands: [Operand; N],
	) -> Operand {
		self.level_to_operand.extend(operands);
		let result = self.generate(preblock, (*binder.body).clone());
		self.level_to_operand.truncate(self.level_to_operand.len() - N);
		result
	}

	fn generate_operation<const N: usize>(
		&mut self,
		preblock: &mut Preblock,
		values: [ClosedValue; N],
		operation: impl FnOnce([Operand; N]) -> Operation,
	) -> Operand {
		let operands = values.map(|value| self.generate(preblock, value));
		let register = self.symbol_generator.generate();
		preblock.statements.push(Statement::Assign(register, operation(operands)));
		Operand::Load(Load::reg(Register::Local(register)))
	}

	fn generate_unary_operation(
		&mut self,
		preblock: &mut Preblock,
		value: ClosedValue,
		operation: impl FnOnce(Operand) -> Operation,
	) -> Operand {
		let operand = self.generate(preblock, value);
		let register = self.symbol_generator.generate();
		preblock.statements.push(Statement::Assign(register, operation(operand)));
		Operand::Load(Load::reg(Register::Local(register)))
	}

	fn generate_variable(&self, variable: Variable) -> Operand {
		match variable {
			Variable::Outer(level) => Operand::Load(Load::reg(Register::Outer(level))),
			Variable::Parameter => Operand::Load(Load::reg(Register::Parameter)),
			Variable::Local(level) => self.level_to_operand[level.0].clone(),
		}
	}

	fn generate_function(&mut self, preblock: &mut Preblock, function: Function) -> Operand {
		let operation = Operation::Function {
			captures: function
				.captures
				.into_iter()
				.map(|variable| self.generate_variable(variable))
				.collect::<Vec<_>>(),
			procedure_index: function.procedure_id,
		};
		let register = self.symbol_generator.generate();
		preblock.statements.push(Statement::Assign(register, operation));
		Operand::Load(Load::reg(Register::Local(register)))
	}

	// Takes a contextual preblock and a value, modifies the preblock, and returns the modified preblock with an operand representing that value.
	pub fn generate(&mut self, preblock: &mut Preblock, value: ClosedValue) -> Operand {
		match value {
			// Control-Flow Constructs
			ClosedValue::Let { ty: _, argument, tail } => {
				// TODO: We might need to pass `ty` to each call of this function.
				let assignee_operand = self.generate(preblock, (*argument).clone());
				self.generate_with(preblock, tail, [assignee_operand])
			}
			// TODO: This looks like it needs heavy refactoring.
			ClosedValue::CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let scrutinee_operand = self.generate(preblock, *scrutinee);
				let initial_operand = self.generate(preblock, *case_nil);
				let is_positive_symbol = self.symbol_generator.generate();
				preblock
					.statements
					.push(Statement::Assign(is_positive_symbol, Operation::Id(scrutinee_operand.clone())));

				let result_symbol = self.symbol_generator.generate();
				let prev_preblock = std::mem::replace(
					preblock,
					Preblock {
						label: self.symbol_generator.generate(),
						parameters: vec![result_symbol],
						statements: vec![],
					},
				);

				let count_symbol = self.symbol_generator.generate();
				let accumulator_symbol = self.symbol_generator.generate();
				let mut loop_preblock = Preblock {
					label: self.symbol_generator.generate(),
					parameters: vec![count_symbol, accumulator_symbol],
					statements: vec![],
				};
				self.terminate(
					prev_preblock,
					Terminator::Branch {
						operand: Operand::Load(Load::reg(Register::Local(is_positive_symbol))),
						false_block: preblock.label,
						false_operands: vec![initial_operand.clone()],
						true_block: loop_preblock.label,
						true_operands: vec![scrutinee_operand, initial_operand],
					},
				);

				let new_accumulator = self.generate_with(
					&mut loop_preblock,
					case_suc,
					[
						Operand::Load(Load::reg(Register::Local(count_symbol))),
						Operand::Load(Load::reg(Register::Local(accumulator_symbol))),
					],
				);
				let new_count_symbol = self.symbol_generator.generate();
				loop_preblock.statements.push(Statement::Assign(
					new_count_symbol,
					Operation::Pred(Operand::Load(Load::reg(Register::Local(count_symbol)))),
				));
				let is_new_count_positive_symbool = self.symbol_generator.generate();
				loop_preblock.statements.push(Statement::Assign(
					is_new_count_positive_symbool,
					Operation::IsPositive(Operand::Load(Load::reg(Register::Local(new_count_symbol)))),
				));
				let loop_preblock_label = loop_preblock.label;
				self.terminate(
					loop_preblock,
					Terminator::Branch {
						operand: Operand::Load(Load::reg(Register::Local(is_new_count_positive_symbool))),
						false_block: preblock.label,
						false_operands: vec![new_accumulator.clone()],
						true_block: loop_preblock_label,
						true_operands: vec![
							Operand::Load(Load::reg(Register::Local(new_count_symbol))),
							new_accumulator,
						],
					},
				);

				Operand::Load(Load::reg(Register::Local(result_symbol)))
			}
			ClosedValue::CaseBool { scrutinee, motive: _, case_false, case_true } => {
				let scrutinee_operand = self.generate(preblock, *scrutinee);

				let mut false_preblock =
					Preblock { label: self.symbol_generator.generate(), parameters: vec![], statements: vec![] };
				let mut true_preblock =
					Preblock { label: self.symbol_generator.generate(), parameters: vec![], statements: vec![] };
				let result_operand = self.symbol_generator.generate();

				// TODO: Use `motive` here to name the preblock parameter.
				let prev_preblock = std::mem::replace(
					preblock,
					Preblock {
						label: self.symbol_generator.generate(),
						parameters: vec![result_operand],
						statements: vec![],
					},
				);
				self.terminate(
					prev_preblock,
					Terminator::Branch {
						operand: scrutinee_operand,
						false_block: false_preblock.label,
						false_operands: vec![],
						true_block: true_preblock.label,
						true_operands: vec![],
					},
				);

				let false_operand = self.generate(&mut false_preblock, *case_false);
				let true_operand = self.generate(&mut true_preblock, *case_true);

				self.terminate(
					false_preblock,
					Terminator::Jump { block: Some(preblock.label), operand: false_operand },
				);
				self.terminate(
					true_preblock,
					Terminator::Jump { block: Some(preblock.label), operand: true_operand },
				);

				Operand::Load(Load::reg(Register::Local(result_operand)))
			}

			// Variables
			ClosedValue::Variable(variable) => self.generate_variable(variable),

			// Literals
			ClosedValue::Universe(k) => Operand::Literal(Literal::Universe(k)),
			ClosedValue::Bool => Operand::Literal(Literal::Bool),
			ClosedValue::Nat => Operand::Literal(Literal::Nat),
			ClosedValue::Num(n) => Operand::Literal(Literal::Num(n)),
			ClosedValue::BoolValue(b) => Operand::Literal(Literal::BoolValue(b)),

			// Modifiers
			ClosedValue::Project(value, projection) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::Projection(projection)),
			ClosedValue::Unwrap(value) => self.generate(preblock, (*value).clone()).modify(Modifier::Unwrap),
			ClosedValue::UnRc(value) => self.generate(preblock, (*value).clone()).modify(Modifier::UnRc),

			// Binding Operations
			ClosedValue::Function(function) => self.generate_function(preblock, function),

			ClosedValue::Pi(base, family) => {
				let base = self.generate(preblock, *base);
				let family = self.generate_function(preblock, family);
				let register = self.symbol_generator.generate();
				preblock.statements.push(Statement::Assign(register, Operation::Pi { base, family }));
				Operand::Load(Load::reg(Register::Local(register)))
			}
			ClosedValue::Sigma(base, family) => {
				let base = self.generate(preblock, *base);
				let family = self.generate_function(preblock, family);
				let register = self.symbol_generator.generate();
				preblock.statements.push(Statement::Assign(register, Operation::Sigma { base, family }));
				Operand::Load(Load::reg(Register::Local(register)))
			}

			// Operations
			ClosedValue::Pair { basepoint, fiberpoint } =>
				self.generate_operation(preblock, [*basepoint, *fiberpoint], |[basepoint, fiberpoint]| {
					Operation::Pair { basepoint, fiberpoint }
				}),
			ClosedValue::Apply { callee, argument } => {
				let result_symbol = self.symbol_generator.generate();
				let callee = self.generate(preblock, *callee);
				let argument = self.generate(preblock, *argument);

				let prev_preblock = std::mem::replace(
					preblock,
					Preblock {
						label: self.symbol_generator.generate(),
						parameters: vec![result_symbol],
						statements: vec![],
					},
				);

				self.terminate(
					prev_preblock,
					Terminator::Apply { callee, argument, return_block: preblock.label },
				);

				Operand::Load(Load::reg(Register::Local(result_symbol)))
			}
			ClosedValue::Suc(value) => self.generate_unary_operation(preblock, *value, Operation::Suc),
			ClosedValue::WrapType(value) => self.generate_unary_operation(preblock, *value, Operation::WrapType),
			ClosedValue::WrapNew(value) => self.generate_unary_operation(preblock, *value, Operation::WrapNew),
			ClosedValue::RcType(value) => self.generate_unary_operation(preblock, *value, Operation::RcType),
			ClosedValue::RcNew(value) => self.generate_unary_operation(preblock, *value, Operation::RcNew),
		}
	}
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
