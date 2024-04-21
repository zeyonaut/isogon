use std::{collections::HashMap, iter::repeat};

use crate::{
	common::{ArraySize, Binder, Cpy, Field, Label},
	ir::{
		flat::{self, Term, Variable},
		linear::{
			Block, Frame, Framed, Layout, Load, Operation, Procedure, Program, Projector, Prototype, Register,
			Statement, Symbol, SymbolGenerator, Terminator, Value,
		},
	},
};

/// Converts a hoisted program into a control-flow graph representation.
pub fn linearize(program: flat::Program) -> Program {
	let entry = build_procedure(program.entry);

	let procedures = program
		.procedures
		.into_iter()
		.map(|procedure| {
			(
				Prototype {
					outer: procedure
						.captured_parameters
						.into_iter()
						.map(|x| (x.name, x.repr.as_ref().map(Into::into)))
						.collect(),
					parameter: (procedure.parameter.name, procedure.parameter.repr.as_ref().map(Into::into)),
					result: procedure.result_repr.as_ref().map(Into::into),
				},
				build_procedure(procedure.body),
			)
		})
		.collect::<Vec<_>>();

	Program { entry, procedures }
}

enum ValueProducer {
	Value(Value),
	Exp(usize, Option<Layout>, Value),
}

impl ValueProducer {
	fn next(&mut self) -> Value {
		match self {
			Self::Value(complex) => complex.clone(),
			Self::Exp(n, layout, complex) => {
				let result = complex.project(Projector::Exp(*n, layout.clone()));
				*n += 1;
				result
			}
		}
	}
}

struct ProcedureBuilder {
	register_context: RegisterContext,
	local_symbol_generator: SymbolGenerator,
	level_to_producer: Vec<ValueProducer>,
	blocks: Vec<Block>,
}

fn build_procedure(value: Term) -> Procedure {
	let mut builder = ProcedureBuilder::new(vec![], None);

	let ([], entry) = builder.block([]);
	if let Some(result) = builder.generate(entry, &value) {
		let (entry, operand) = result.unframe();
		builder.terminate(entry, Terminator::Return(operand));
	}

	Procedure { blocks: builder.blocks }
}

struct RegisterContext {
	outer: Vec<Option<Layout>>,
	parameter: Option<Option<Layout>>,
	local: HashMap<Symbol, Option<Layout>>,
}

impl RegisterContext {
	pub fn get(&self, register: Register) -> Option<Layout> {
		match register {
			Register::Outer(level) => self.outer[level.0].clone(),
			Register::Parameter => self.parameter.as_ref().unwrap().clone(),
			Register::Local(local) => self.local[&local].clone(),
		}
	}
}

impl ProcedureBuilder {
	fn new(outer: Vec<Option<Layout>>, parameter: Option<Option<Layout>>) -> Self {
		Self {
			register_context: RegisterContext { outer, parameter, local: HashMap::new() },
			local_symbol_generator: SymbolGenerator::new(),
			level_to_producer: vec![],
			blocks: Vec::new(),
		}
	}

	pub fn block<const N: usize>(&mut self, reprs: [Option<Layout>; N]) -> ([Symbol; N], Frame) {
		let id = self.blocks.len();
		let reprs = reprs.map(|r| (self.local_symbol_generator.generate(), r));
		let names = reprs.each_ref().map(|(n, _)| *n);
		self.blocks.push(Block::new(reprs.into()));
		(names, Frame(id))
	}

	pub fn append(&mut self, Frame(id): &Frame, statement: Statement) {
		assert!(self.blocks[*id].terminator.is_none());
		self.blocks[*id].statements.push(statement);
	}

	pub fn terminate(&mut self, Frame(id): Frame, terminator: Terminator) {
		assert!(self.blocks[id].terminator.is_none());
		self.blocks[id].terminator = Some(terminator);
	}

	pub fn terminate_jump(&mut self, destination: &Frame, value: Framed<Box<[Value]>>) {
		let (frame, result) = value.unframe();
		self.terminate(frame, Terminator::Jump(destination.id(), result))
	}

	pub fn generate_many_ref<'a>(
		&mut self,
		frame: Frame,
		terms: impl Iterator<Item = &'a Term>,
	) -> Option<Framed<Box<[Value]>>> {
		let mut frame = frame;
		let mut values = Vec::new();
		for term in terms.into_iter() {
			let (frame_new, value) = self.generate(frame.clone(), term)?.unframe();
			frame = frame_new;
			values.push(value);
		}
		Some(frame.and(values.into()))
	}

	pub fn generate_many(
		&mut self,
		frame: Frame,
		terms: impl Iterator<Item = Term>,
	) -> Option<Framed<Box<[Value]>>> {
		let mut frame = frame;
		let mut values = Vec::new();
		for term in terms.into_iter() {
			let (frame_new, value) = self.generate(frame.clone(), &term)?.unframe();
			frame = frame_new;
			values.push(value);
		}
		Some(frame.and(values.into()))
	}

	#[must_use]
	pub fn generate(&mut self, frame: Frame, term: &Term) -> Option<Framed<Value>> {
		Some(match term {
			Term::Irrelevant => frame.and(Value::None),

			Term::Variable(_name, variable) => frame.and(match variable {
				Variable::Outer(level) => Register::Outer(*level).into(),
				Variable::Parameter => Register::Parameter.into(),
				Variable::Local(level) => self.level_to_producer[level.0].next(),
			}),

			Term::Let { grade, argument_repr: _, argument, tail } =>
				if *grade == 0 {
					self.generate_with(frame, tail, [Value::None].map(ValueProducer::Value))?
				} else if *grade == 1 {
					let (frame, argument) = self.generate(frame, argument)?.unframe();
					self.generate_with(frame, tail, [argument].map(ValueProducer::Value))?
				} else {
					unimplemented!();
				},

			Term::Repeat { grade, copy, term } => {
				let (frame, many) = self.generate_many_ref(frame, repeat(term.as_ref()).take(*grade))?.unframe();
				match copy {
					Cpy::Tr =>
						if many.len() == 0 {
							frame.and(Value::None)
						} else {
							frame.and(many.into_vec().into_iter().next().unwrap())
						},
					Cpy::Nt => frame.and(Value::Array(many)),
				}
			}
			Term::ExpLet { grade, grade_argument: _, copy, repr, argument, tail } =>
				if *grade == 0 {
					self.generate_with(frame, tail, [Value::None].map(ValueProducer::Value))?
				} else if *grade == 1 {
					let (frame, argument) = self.generate(frame, argument)?.unframe();
					match copy {
						Cpy::Tr => self.generate_with(frame, tail, [ValueProducer::Value(argument)])?,
						Cpy::Nt => self.generate_with(
							frame,
							tail,
							[ValueProducer::Exp(0, repr.as_ref().map(Into::into), argument)],
						)?,
					}
				} else {
					unimplemented!();
				},

			Term::Function { procedure_id, captures } => {
				let (frame, captures) = self
					.generate_many(frame, captures.iter().map(|c| Term::Variable(None, c.variable)))?
					.unframe();
				let captures = Register::Local(self.assign(&frame, Operation::Captures(captures)));
				frame.and(Value::function(Value::Procedure(*procedure_id), captures))
			}
			Term::Apply { callee, argument, result_repr } => {
				let (frame, callee) = self.generate(frame, callee)?.unframe();
				let (frame, argument) = self.generate(frame, argument)?.unframe();
				let ([result], later) = self.block([result_repr.as_ref().map(Into::into)]);
				self.terminate(
					frame,
					Terminator::Apply {
						procedure: callee.project(Projector::Procedure),
						captures: callee.project(Projector::Captures),
						argument,
						later: later.id(),
					},
				);
				later.and(Register::Local(result).into())
			}

			Term::Pair { basepoint, fiberpoint } => {
				let (frame, basepoint) = self.generate(frame, basepoint)?.unframe();
				let (frame, fiberpoint) = self.generate(frame, fiberpoint)?.unframe();
				frame.and(Value::pair(basepoint, fiberpoint))
			}
			Term::SgLet { grade, argument, bound_reprs, tail } =>
				if *grade == 0 {
					self.generate_with(frame, tail, [Value::None, Value::None].map(ValueProducer::Value))?
				} else if *grade == 1 {
					let (frame, argument) = self.generate(frame, argument)?.unframe();
					let bound_reprs = bound_reprs.each_ref().map(|x| x.as_ref().map(Into::into));
					self.generate_with(
						frame,
						tail,
						[
							argument.project(Projector::Field(Field::Base, bound_reprs.clone())),
							argument.project(Projector::Field(Field::Fiber, bound_reprs.clone())),
						]
						.map(ValueProducer::Value),
					)?
				} else {
					unimplemented!();
				},

			Term::EnumValue(k, v) => frame.and(Value::Enum(*k, *v)),
			Term::CaseEnum { scrutinee, cases, motive_repr } => {
				let (frame, scrutinee) = self.generate(frame, scrutinee)?.unframe();
				match cases.len() {
					0 => {
						self.terminate(frame, Terminator::Abort);
						return None;
					}
					1 => self.generate(frame, &cases[0])?,
					_ => {
						let (entry_frames, case_exits): (Vec<_>, Vec<_>) = cases
							.iter()
							.map(|term| {
								let ([], block) = self.block([]);
								(block.id(), self.generate(block, term))
							})
							.unzip();
						self.terminate(frame, Terminator::Split(scrutinee, entry_frames.into()));
						let ([result], frame) = self.block([motive_repr.as_ref().map(Into::into)]);
						for case_exit in case_exits.into_iter().flatten() {
							self.terminate_jump(&frame, case_exit.map(|x| vec![x].into()));
						}
						frame.and(Register::Local(result).into())
					}
				}
			}

			Term::Num(n) => frame.and(Value::Num(*n)),
			Term::Suc(term) => {
				let (frame, n) = self.generate(frame, term)?.unframe();
				let successor = match n {
					Value::Num(n) => Value::Num(n.checked_add(1).unwrap()),
					Value::Load(load) => {
						let successor = self.assign(&frame, Operation::Suc(load));
						Register::Local(successor).into()
					}
					_ => panic!(),
				};
				frame.and(successor)
			}
			Term::CaseNat { scrutinee, case_nil, case_suc, motive_repr } => {
				let (frame, limit) = self.generate(frame, scrutinee)?.unframe();
				let initial = self.generate(frame, case_nil)?;
				let ([c_index, c_previous], condition_check) =
					self.block([Some(Layout::Nat), motive_repr.as_ref().map(Into::into)]);
				self.terminate_jump(&condition_check, initial.map(|x| vec![Value::Num(0), x].into()));
				let ([b_index, b_previous], body) =
					self.block([Some(Layout::Nat), motive_repr.as_ref().map(Into::into)]);
				let ([result], frame) = self.block([motive_repr.as_ref().map(Into::into)]);
				self.terminate(
					condition_check.clone(),
					Terminator::CaseNat {
						index: Register::Local(c_index).into(),
						limit,
						body: body.id(),
						body_args: [c_index, c_previous].map(Register::Local).map(Into::into),
						exit: frame.id(),
						exit_arg: Register::Local(c_previous).into(),
					},
				);
				let (body, value) = self
					.generate_with(
						body,
						case_suc,
						[b_index, b_previous].map(Register::Local).map(Into::into).map(ValueProducer::Value),
					)?
					.unframe();
				let b_suc = self.assign(&body, Operation::Suc(Load::reg(Register::Local(b_index))));
				self
					.terminate_jump(&condition_check, body.and(vec![Register::Local(b_suc).into(), value].into()));
				frame.and(Register::Local(result).into())
			}

			Term::BxValue(term) => {
				let (frame, inner) = self.generate(frame, term)?.unframe();
				let inner = self.assign(&frame, Operation::Alloc(inner));
				frame.and(Register::Local(inner).into())
			}
			Term::BxProject(term, repr) => {
				let (frame, term) = self.generate(frame, term)?.unframe();
				let inner =
					self.assign(&frame, Operation::Id(term.project(Projector::Bx(repr.as_ref().map(Into::into)))));
				let Value::Load(load) = term else { panic!() };
				self.append(&frame, Statement::Free(load));
				frame.and(Register::Local(inner).into())
			}

			Term::WrapValue(term) => self.generate(frame, term)?.map(|x| Value::Wrap(x.into())),
			Term::WrapProject(term, repr) =>
				self.generate(frame, term)?.map(|x| x.project(Projector::Wrap(repr.as_ref().map(Into::into)))),
		})
	}

	pub fn generate_with<const N: usize>(
		&mut self,
		frame: Frame,
		binder: &Binder<Label, Box<Term>, N>,
		values: [ValueProducer; N],
	) -> Option<Framed<Value>> {
		let len = self.level_to_producer.len();
		self.level_to_producer.extend(values);
		let result = self.generate(frame, &binder.body);
		self.level_to_producer.truncate(len);
		result
	}

	// Create a new register from an assignment and return its symbol.
	fn assign(&mut self, frame: &Frame, operation: Operation) -> Symbol {
		let repr = self.layout_of_operation(&operation);
		let symbol = self.local_symbol_generator.generate();
		self.register_context.local.insert(symbol, repr);
		self.append(frame, Statement::Assign(symbol, operation));
		symbol
	}

	fn layout_of_operation(&self, operation: &Operation) -> Option<Layout> {
		match operation {
			Operation::Id(value) => self.layout_of_value(value),
			Operation::Alloc(_) => Some(Layout::Ptr),
			Operation::Captures(_) => Some(Layout::Ptr),
			Operation::Suc(_) => Some(Layout::Nat),
		}
	}

	fn layout_of_value(&self, value: &Value) -> Option<Layout> {
		match value {
			Value::None => None,
			Value::Num(_) => Some(Layout::Nat),
			Value::Enum(_, _) => Some(Layout::Byte),
			Value::Procedure(_) => Some(Layout::Ptr),
			Value::Load(load) => self.layout_of_load(load),
			Value::Function { .. } => Some(Layout::Fun),
			Value::Array(values) => match values.len() {
				0 => None,
				1 => self.layout_of_value(values.first().unwrap()),
				n => Some(Layout::Array(ArraySize(n), self.layout_of_value(values.first().unwrap())?.into())),
			},
			Value::Pair(left, right) => {
				let left = self.layout_of_value(left);
				let right = self.layout_of_value(right);
				match (left, right) {
					(None, right) => right,
					(left, None) => left,
					(Some(left), Some(right)) => Some(Layout::Pair([left, right].into())),
				}
			}
			Value::Wrap(value) => self.layout_of_value(value),
		}
	}

	fn layout_of_load(&self, load: &Load) -> Option<Layout> {
		if load.projectors.is_empty() {
			self.register_context.get(load.register)
		} else {
			match load.projectors.last().unwrap() {
				Projector::Exp(_, layout) => layout.clone(),
				Projector::Procedure => Some(Layout::Ptr),
				Projector::Captures => Some(Layout::Ptr),
				Projector::Field(Field::Base, [base, _]) => base.clone(),
				Projector::Field(Field::Fiber, [_, fiber]) => fiber.clone(),
				Projector::Bx(layout) => layout.clone(),
				Projector::Wrap(layout) => layout.clone(),
			}
		}
	}
}
