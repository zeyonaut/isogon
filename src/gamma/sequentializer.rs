use std::{collections::HashMap, hash::Hash};

use super::{
	closer::{ClosedValue, Function, Variable},
	common::{Binder, Copyability, Level, Name, Projection, Repr, UniverseKind},
};

struct ProcedureBuilder {
	symbol_generator: SymbolGenerator,
	level_to_operand: Vec<Operand>,
	blocks: HashMap<Symbol, Block>,
}

struct Program {
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
	Branch { operand: Operand, false_block: Symbol, true_block: Symbol },
	Jump { block: Option<Symbol>, operand: Operand },
}

enum Statement {
	Assign(Symbol, Operation),
	Define(Symbol, Block),
}

enum Operation {
	Function { captures: Vec<Operand>, procedure_index: usize },
	Pi { base: Operand, family: Operand },
	Sigma { base: Operand, family: Operand },
	Id(Operand),
	Pair { basepoint: Operand, fiberpoint: Operand },
	Apply { callee: Operand, argument: Operand },
	Suc(Operand),
	WrapType(Operand),
	WrapNew(Operand),
	RcType(Operand),
	RcNew(Operand),
}

#[derive(Clone)]
enum Literal {
	Nat,
	Bool,
	Universe(UniverseKind),
	Num(usize),
	BoolValue(bool),
	Function { block: Symbol },
}

#[derive(Clone)]
enum Operand {
	Literal(Literal),
	Load(Load),
}

impl Operand {
	pub fn modify(mut self, modifier: Modifier) -> Self {
		match self {
			// TODO: Should we allow arbitrarily complex literals at this stage?
			Operand::Literal(literal) => unimplemented!(),
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

pub fn sequentialize(program: super::closer::Program) -> Program {
	let entry = build_procedure(program.entry);

	let mut procedures = program
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
			ClosedValue::Let { ty, argument, tail } => {
				// TODO: We might need to pass `ty` to each call of this function.
				let assignee_operand = self.generate(preblock, (*argument).clone());
				self.generate_with(preblock, tail, [assignee_operand])
			}
			ClosedValue::CaseNat { scrutinee, motive, case_nil, case_suc } => {
				unimplemented!()
			}
			ClosedValue::CaseBool { scrutinee, motive, case_false, case_true } => {
				let scrutinee_operand = self.generate(preblock, (*scrutinee).clone());

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
						true_block: true_preblock.label,
					},
				);

				let false_operand = self.generate(&mut false_preblock, (*case_false).clone());
				let true_operand = self.generate(&mut true_preblock, (*case_true).clone());

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
			ClosedValue::Apply { callee, argument } =>
				self.generate_operation(preblock, [*callee, *argument], |[callee, argument]| Operation::Apply {
					callee,
					argument,
				}),
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
