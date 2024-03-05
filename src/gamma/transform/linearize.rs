use std::collections::HashMap;

use crate::gamma::{
	common::{Binder, Copyability, Field, Repr, ReprAtom, UniverseKind},
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
	let _entry = build_procedure(program.entry);

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
	let mut builder = ProcedureBuilder::new(vec![], None);

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
	const BYTE: Self = Self::new(None, Some(Repr::Atom(ReprAtom::Byte)));
	const NONE: Self = Self::new(None, None);
	const PI: Self = Self::new(Some(Class::Pi), Some(Repr::Atom(ReprAtom::Fun)));

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

	// Create a new register from an assignment and return its symbol.
	fn assign(&mut self, preblock: &mut Preblock, operation: Operation) -> Symbol {
		let ty = self.generate_type_from_operation(preblock, &operation);
		self.assign_with_type(preblock, operation, ty)
	}

	fn assign_with_type(&mut self, preblock: &mut Preblock, operation: Operation, ty: RegisterType) -> Symbol {
		let symbol = self.register_register(ty);
		preblock.statements.push(Statement::Assign(symbol, operation));
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
		Operand::Load(Load::reg(Register::Local(self.assign(preblock, operation(operands)))))
	}

	fn generate_unary_operation(
		&mut self,
		preblock: &mut Preblock,
		value: Term,
		operation: impl FnOnce(Operand) -> Operation,
	) -> Operand {
		let operand = self.generate(preblock, value);
		Operand::Load(Load::reg(Register::Local(self.assign(preblock, operation(operand)))))
	}

	fn generate_variable(&self, variable: Variable) -> Operand {
		match variable {
			Variable::Outer(level) => Operand::Load(Load::reg(Register::Outer(level))),
			Variable::Parameter => Operand::Load(Load::reg(Register::Parameter)),
			Variable::Local(level) => self.level_to_operand[level.0].clone(),
		}
	}

	fn generate_function(&mut self, preblock: &mut Preblock, function: Function) -> Operand {
		Operand::Load(Load::reg(Register::Local(
			self.assign(
				preblock,
				Operation::Function {
					captures: function
						.captures
						.into_iter()
						.map(|variable| self.generate_variable(variable))
						.collect::<Vec<_>>(),
					procedure_index: function.procedure_id,
				},
			),
		)))
	}

	pub fn drop_all(&mut self, preblock: &mut Preblock, expiring_variables: Vec<Symbol>) {
		// We destroy each register in the reverse order of allocation.
		for var in expiring_variables.into_iter().rev() {
			// NOTE: expiring variables should always be registered and nontrivial.
			let _class = self.register_context.local.get(&var).unwrap().class.clone().unwrap();

			let prev_preblock = std::mem::replace(
				preblock,
				Preblock { label: self.symbol_generator.generate(), parameters: vec![], statements: vec![] },
			);

			self.terminate(prev_preblock, Terminator::Drop { block: preblock.label, variable: var });

			// Generate a new block.
			todo!();
		}
	}

	// Takes a contextual preblock and a value, modifies the preblock, and returns the modified preblock with an operand representing that value.
	pub fn generate(&mut self, preblock: &mut Preblock, value: Term) -> Operand {
		match value {
			Term::Let { ty: _, argument, tail } => {
				let scope = self.unhandled_locals.len();
				let argument = self.generate(preblock, (*argument).clone());
				let argument_expirees = self.unhandled_locals.drain(scope..).collect::<Vec<_>>();
				let mut argument_ty = self.generate_type_from_operand(preblock, &argument);

				// Rebase the assignee's class in terms of new non-expiring registers (if necessary).
				// TODO: is it better when renewing to reassign expiring registers, or extend their lifetime?
				if let Some(class) = &mut argument_ty.class {
					self.renew_class(preblock, class, &argument_expirees);
				}

				let argument = self.assign_with_type(preblock, Operation::Id(argument), argument_ty);

				// Perform any drops generated from the argument.
				self.drop_all(preblock, argument_expirees);

				let operand =
					self.generate_with(preblock, tail, [Operand::Load(Load::reg(Register::Local(argument)))]);

				let body_expirees = self.unhandled_locals.drain(scope..).collect::<Vec<_>>();

				// FIXME: Wait, so we can't drop these yet - this would affect the operand.
				// Defer to the next let-expression/positive eliminator/function call (both in callee and argument position?)
				self.drop_all(preblock, body_expirees);

				todo!()
			}

			Term::Apply { callee, argument, fiber_representation, family } => {
				todo!()
			}
			Term::CaseEnum { scrutinee, cases, fiber_representation, motive } => {
				todo!()
			}

			Term::CaseNat { scrutinee, case_nil, case_suc, fiber_representation, motive } => {
				todo!()
			}

			// Variables
			Term::Variable(variable) => self.generate_variable(variable),

			// Literals
			Term::Universe(k) => match k.0 {
				Copyability::Nontrivial => Operand::Literal(Literal::Class),
				Copyability::Trivial => Operand::Literal(Literal::None),
			},
			Term::Nat => Operand::Literal(Literal::Nat),
			Term::Num(n) => Operand::Literal(Literal::Num(n)),
			Term::Enum(_) => Operand::Literal(Literal::None),
			Term::EnumValue(k, v) => Operand::Literal(Literal::EnumValue(k, v)),

			// Modifiers
			Term::Project(value, projection, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::Projection(projection, universe)),
			Term::Unwrap(value, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::Unwrap(universe)),
			Term::UnRc(value, universe) =>
				self.generate(preblock, (*value).clone()).modify(Modifier::UnRc(universe)),

			// Binding Operations
			Term::Function(function) => self.generate_function(preblock, function),

			Term::Pi { base, family, .. } => Operand::Literal(Literal::Pi),
			Term::Sigma { base_universe, base, family_universe, family } => {
				let base = self.generate(preblock, *base);
				let family = self.generate_function(preblock, family);
				Operand::Load(Load::reg(Register::Local(
					self.assign(preblock, Operation::Sigma { base_universe, base, family_universe, family }),
				)))
			}

			// Operations
			Term::Pair { basepoint, fiberpoint } =>
				self.generate_operation(preblock, [*basepoint, *fiberpoint], |[basepoint, fiberpoint]| {
					Operation::Pair { basepoint, fiberpoint }
				}),

			// Unary Operations
			Term::Suc(value) => self.generate_unary_operation(preblock, *value, Operation::Suc),
			Term::WrapType(value) => self.generate_unary_operation(preblock, *value, Operation::WrapClass),
			Term::WrapNew(value) => self.generate_unary_operation(preblock, *value, Operation::WrapNew),
			Term::RcType(value) => self.generate_unary_operation(preblock, *value, Operation::SharedClass),
			Term::RcNew(value) => self.generate_unary_operation(preblock, *value, Operation::RcNew),
		}
	}

	fn generate_type_from_operation(
		&mut self,
		preblock: &mut Preblock,
		operation: &Operation,
	) -> RegisterType {
		match operation {
			Operation::Function { .. } => RegisterType::PI,
			Operation::Sigma { base_universe, family_universe, .. } =>
				if Copyability::Nontrivial == base_universe.0.max(family_universe.0) {
					RegisterType::CLASS
				} else {
					RegisterType::NONE
				},

			// 2-ary
			Operation::Pair { basepoint, fiberpoint } => {
				let base = self.generate_type_from_operand(preblock, basepoint);
				let fiber =  self.generate_type_from_operand(preblock, fiberpoint);
				let class = if base.class.is_none() && fiber.class.is_none() {
					None
				} else {
					Some(Class::Pair { base: base.class.map(Box::new), base_repr: base.repr.clone(), fiber: fiber.class.map(Box::new) })
				};
				RegisterType::new(class, Repr::pair(base.repr, fiber.repr))
			}

			// 1-ary.
			Operation::Id(operand) => self.generate_type_from_operand(preblock, operand).into(),
			Operation::WrapNew(operand) => {
				let ty = self.generate_type_from_operand(preblock, operand);
				RegisterType::new(Some(Class::Wrap(ty.class.map(Box::new))), ty.repr)
			}
			Operation::RcNew(operand) => {
				let ty = self.generate_type_from_operand(preblock, operand);
				RegisterType::new(
					Some(Class::Shared(ty.class.map(Box::new))),
					Some(Repr::Atom(ReprAtom::Pointer)),
				)
			}
			Operation::IsPositive(_) => RegisterType::BYTE,
			Operation::Pred(_) | Operation::Suc(_) => RegisterType::NAT,

			Operation::WrapClass(_) |
			Operation::SharedClass(_) |
			Operation::PairClass { .. } |
			// NOTE: The following are only generated when known to be nontrivial.
			Operation::WrapClassInner(_) |
			Operation::SharedClassInner(_) |
			Operation::PairClassProjection(_, _) => RegisterType::CLASS,
		}
	}

	fn generate_type_from_operand(&mut self, preblock: &mut Preblock, operand: &Operand) -> RegisterType {
		match operand {
			Operand::Literal(literal) => match literal {
				Literal::None => RegisterType::NONE,
				Literal::Nat => RegisterType::CLASS,
				Literal::Pi => RegisterType::CLASS,
				Literal::Class => RegisterType::CLASS,
				Literal::Num(_) => RegisterType::NAT,
				Literal::EnumValue(..) => RegisterType::BYTE,
			},
			Operand::Load(load) => {
				let ty = self.register_context.get(load.register);

				let repr = load
					.modifiers
					.last()
					.map(|last| match last {
						Modifier::Projection(_, universe) => universe.1.clone(),
						Modifier::UnRc(universe) => universe.1.clone(),
						Modifier::Unwrap(universe) => universe.1.clone(),
					})
					.unwrap_or(ty.repr);

				let class = ty.class.and_then(|mut class| {
					if load
						.modifiers
						.last()
						.map(|last| match last {
							Modifier::Projection(_, UniverseKind(Copyability::Trivial, _))
							| Modifier::UnRc(UniverseKind(Copyability::Trivial, _))
							| Modifier::Unwrap(UniverseKind(Copyability::Trivial, _)) => true,
							_ => false,
						})
						.unwrap_or(false)
					{
						None
					} else {
						// NOTE: Once an operand is encountered as a class, every subsequent match should be an operand (by construction). In addition, once a trivial modifier is encountered, every subsequent modifier must be trivial; since, in this branch, the last modifier is nontrivial, then all modifiers must be nontrivial, justifying the unwraps.
						for modifier in &load.modifiers {
							class = match modifier {
								Modifier::Projection(projection, _) => match class {
									Class::Operand(operand) =>
										Class::Operand(Operand::Load(Load::reg(Register::Local(
											self.assign(preblock, Operation::PairClassProjection(operand, *projection)),
										)))),
									Class::Pair { base, base_repr, fiber } => match projection {
										Field::Base => *base.unwrap(),
										Field::Fiber => *fiber.unwrap(),
									},
									_ => panic!("invalid modifier"),
								},
								Modifier::UnRc(_) => match class {
									Class::Operand(operand) => Class::Operand(Operand::Load(Load::reg(
										Register::Local(self.assign(preblock, Operation::SharedClassInner(operand))),
									))),
									Class::Shared(inner) => *inner.unwrap(),
									_ => panic!("invalid modifier"),
								},
								Modifier::Unwrap(_) => match class {
									Class::Operand(operand) => Class::Operand(Operand::Load(Load::reg(
										Register::Local(self.assign(preblock, Operation::WrapClassInner(operand))),
									))),
									Class::Wrap(inner) => *inner.unwrap(),
									_ => panic!("invalid modifier"),
								},
							};
						}
						Some(class)
					}
				});

				RegisterType::new(class, repr)
			}
		}
	}

	// Convert a class into a class withuot expiring variables.
	fn renew_class(&mut self, preblock: &mut Preblock, class: &mut Class, expiring_variables: &[Symbol]) {
		let mut exp_to_non_exp = HashMap::new();
		match class {
			// FIXME: this is weird; why are we duplicating classes across Literal and Class?
			// Possible fix: put all the nullary ones in Literal.
			// That might not be best, since it doesn't account for Literal::None
			// Possible fix: only allow load operands, not literals!
			Class::Nat | Class::Class | Class::Pi | Class::Operand(Operand::Literal(_)) => (),
			Class::Operand(Operand::Load(l)) =>
				if let Register::Local(r) = l.register {
					// NOTE: This is linear in the size of the expiring set; check if it hurts performance.
					if expiring_variables.contains(&r) {
						exp_to_non_exp.insert(r, self.assign(preblock, Operation::Id(Operand::Load(l.clone()))));
						*l = Load::reg(Register::Local(exp_to_non_exp[&r]));
					}
				},
			Class::Wrap(class) =>
				if let Some(class) = class {
					self.renew_class(preblock, class, expiring_variables);
				},
			Class::Shared(class) =>
				if let Some(class) = class {
					self.renew_class(preblock, class, expiring_variables);
				},
			Class::Pair { base, base_repr, fiber } => {
				if let Some(class) = base {
					self.renew_class(preblock, class, expiring_variables);
				}
				if let Some(class) = fiber {
					self.renew_class(preblock, class, expiring_variables);
				}
			}
		}
	}
}
