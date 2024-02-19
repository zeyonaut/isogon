use std::collections::HashMap;

use crate::gamma::{
	common::{Binder, Copyability, Repr, ReprAtom, UniverseKind},
	ir::{
		closed::{self, Function, Term, Variable},
		linear::{
			Block, Class, Literal, Load, Modifier, Operand, Operation, Procedure, Program, Register, Statement,
			Symbol, SymbolGenerator, Terminator,
		},
	},
};

/// Converts a hoisted program into a control-flow graph representation.
pub fn linearize(program: closed::Program) -> Program {
	let entry = build_procedure(program.entry);

	// TODO: Convert types here to classes.
	// Requires linearized code to compute the operand(s) of the class - prepend to entry, or store separately (and how? one-hole contexts?)
	todo!()
	/*
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
	*/
}

struct Preblock {
	label: Symbol,
	parameters: Vec<Symbol>,
	statements: Vec<Statement>,
}

struct ProcedureBuilder {
	register_context: RegisterContext,
	symbol_generator: SymbolGenerator,
	level_to_operand: Vec<Operand>,
	// Locals that have not been destroyed yet.
	unhandled_locals: Vec<Symbol>,
	blocks: HashMap<Symbol, Block>,
}

fn build_procedure(value: Term) -> Procedure {
	let mut builder = ProcedureBuilder::new(todo!(), todo!());

	let entry_label = builder.symbol_generator.generate();
	let mut preblock = Preblock { label: entry_label, parameters: vec![], statements: vec![] };

	let operand = builder.generate(&mut preblock, value);

	builder.terminate(preblock, Terminator::Jump { block: None, operand });

	Procedure { entry_label, blocks: builder.blocks }
}

#[derive(Clone)]
struct RegisterType {
	class: Option<Class>,
	repr: Option<Repr>,
}

impl RegisterType {
	const fn new(class: Option<Class>, repr: Option<Repr>) -> Self {
		Self { class, repr }
	}

	const NAT: Self = Self::new(Some(Class::Nat), Some(Repr::Atom(ReprAtom::Nat)));
	const CLASS: Self = Self::new(Some(Class::Class), Some(Repr::Atom(ReprAtom::Class)));
	const BOOL: Self = Self::new(None, Some(Repr::Atom(ReprAtom::Byte)));
	const NONE: Self = Self::new(None, None);

	const fn operand(operand: Operand, repr: Option<Repr>) -> Self {
		Self { class: Some(Class::Operand(operand)), repr }
	}
}

struct RegisterContext {
	outer: Vec<RegisterType>,
	parameter: Option<RegisterType>,
	local: HashMap<Symbol, RegisterType>,
}

impl RegisterContext {
	pub fn get(&self, register: Register) -> RegisterType {
		match register {
			Register::Outer(level) => self.outer[level.0].clone(),
			Register::Parameter => self.parameter.as_ref().unwrap().clone(),
			Register::Local(local) => self.local[&local].clone(),
		}
	}
}

impl ProcedureBuilder {
	fn new(outer: Vec<RegisterType>, parameter: Option<RegisterType>) -> Self {
		Self {
			register_context: RegisterContext { outer, parameter, local: HashMap::new() },
			symbol_generator: SymbolGenerator::new(),
			level_to_operand: vec![],
			unhandled_locals: vec![],
			blocks: HashMap::new(),
		}
	}

	fn register_register(&mut self, ty: RegisterType) -> Symbol {
		let symbol = self.symbol_generator.generate();
		self.register_context.local.insert(symbol, ty);
		symbol
	}

	pub fn terminate(&mut self, Preblock { label, parameters, statements }: Preblock, terminator: Terminator) {
		self.blocks.insert(label, Block { parameters, statements, terminator });
	}

	pub fn generate_with<const N: usize>(
		&mut self,
		preblock: &mut Preblock,
		binder: Binder<Box<Term>, N>,
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
		values: [Term; N],
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
		value: Term,
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
	pub fn generate(&mut self, preblock: &mut Preblock, value: Term) -> Operand {
		match value {
			Term::Let { ty: _, argument, tail } => {
				todo!()
			}

			Term::Apply { callee, argument, fiber_representation, family } => {
				todo!()
			}
			Term::CaseBool { scrutinee, case_false, case_true, fiber_representation, motive } => {
				todo!()
			}

			Term::CaseNat { scrutinee, case_nil, case_suc, fiber_representation, motive } => {
				todo!()
			}

			// Variables
			Term::Variable(variable) => self.generate_variable(variable),

			// Literals
			Term::Universe(k) => Operand::Literal(Literal::Universe(k)),
			Term::Bool => Operand::Literal(Literal::Bool),
			Term::Nat => Operand::Literal(Literal::Nat),
			Term::Num(n) => Operand::Literal(Literal::Num(n)),
			Term::BoolValue(b) => Operand::Literal(Literal::BoolValue(b)),

			// Modifiers
			Term::Project(value, projection, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::Projection(projection, universe)),
			Term::Unwrap(value, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::Unwrap(universe)),
			Term::UnRc(value, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::UnRc(universe)),

			// Binding Operations
			Term::Function(function) => self.generate_function(preblock, function),

			Term::Pi { base, family, .. } => {
				let base = self.generate(preblock, *base);
				let family = self.generate_function(preblock, family);
				let register = self.symbol_generator.generate();
				preblock.statements.push(Statement::Assign(register, Operation::Pi { base, family }));
				Operand::Load(Load::reg(Register::Local(register)))
			}
			Term::Sigma { base_universe, base, family_universe, family } => {
				let base = self.generate(preblock, *base);
				let family = self.generate_function(preblock, family);
				let register = self.symbol_generator.generate();
				preblock.statements.push(Statement::Assign(
					register,
					Operation::Sigma { base_universe, base, family_universe, family },
				));
				Operand::Load(Load::reg(Register::Local(register)))
			}

			// Operations
			Term::Pair { basepoint, fiberpoint } =>
				self.generate_operation(preblock, [*basepoint, *fiberpoint], |[basepoint, fiberpoint]| {
					Operation::Pair { basepoint, fiberpoint }
				}),

			// Unary Operations
			Term::Suc(value) => self.generate_unary_operation(preblock, *value, Operation::Suc),
			Term::WrapType(value) => self.generate_unary_operation(preblock, *value, Operation::WrapType),
			Term::WrapNew(value) => self.generate_unary_operation(preblock, *value, Operation::WrapNew),
			Term::RcType(value) => self.generate_unary_operation(preblock, *value, Operation::RcType),
			Term::RcNew(value) => self.generate_unary_operation(preblock, *value, Operation::RcNew),
		}
	}
}
