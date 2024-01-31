use std::collections::HashMap;

use crate::gamma::{
	common::Binder,
	ir::{
		closed::{self, ClosedValue, Function, Variable},
		linear::{
			Block, Literal, Load, Modifier, Operand, Operation, Procedure, Program, Prototype, Register,
			Statement, Symbol, SymbolGenerator, Terminator,
		},
	},
};

struct Preblock {
	label: Symbol,
	parameters: Vec<Symbol>,
	statements: Vec<Statement>,
}

struct ProcedureBuilder {
	symbol_generator: SymbolGenerator,
	level_to_operand: Vec<Operand>,
	blocks: HashMap<Symbol, Block>,
}

pub fn sequentialize(program: closed::Program) -> Program {
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
