use std::collections::HashMap;

use crate::{
	common::{Field, Symbol, SymbolGenerator},
	ir::linear::{
		Block, BlockId, Load, Procedure, Program, Projector, Prototype, Register, Statement, Terminator, Value,
	},
};

pub fn execute(program: &Program) -> (HashMap<Symbol, Data>, Data) {
	let mut executor = Executor::new(program);
	let data = executor.run();
	(executor.heap, data)
}

struct Environment {
	outer: Data,
	parameter: Data,
	procedure_id: Option<usize>,
	locals: HashMap<Symbol, Data>,
}

impl Environment {
	fn new(outer: Data, parameter: Data, procedure_id: Option<usize>) -> Self {
		Self { outer, parameter, procedure_id, locals: HashMap::new() }
	}
}

struct Executor<'a> {
	program: &'a Program,
	continuations: Vec<(Symbol, Environment, BlockId, usize)>,
	heap_generator: SymbolGenerator,
	heap: HashMap<Symbol, Data>,
	environment: Environment,
}

impl<'a> Executor<'a> {
	fn new(program: &'a Program) -> Self {
		Self {
			program,
			continuations: Vec::new(),
			heap_generator: SymbolGenerator::new(),
			heap: HashMap::new(),
			environment: Environment::new(Data::None, Data::None, None),
		}
	}

	fn prototype(&self) -> Option<&'a Prototype> {
		Some(&self.program.procedures[self.environment.procedure_id?].0)
	}

	fn procedure(&self) -> &'a Procedure {
		if let Some(id) = self.environment.procedure_id {
			&self.program.procedures[id].1
		} else {
			&self.program.entry
		}
	}

	fn block(&self, id: usize) -> &'a Block { &self.procedure().blocks[id] }

	fn run(&mut self) -> Data {
		let mut current_block_id = 0;
		let mut current_index = 0;
		let data = 'procedure: loop {
			for (i, statement) in self.block(current_block_id).statements.iter().enumerate().skip(current_index)
			{
				match statement {
					Statement::Assign(symbol, value) => {
						let data = self.compute(value);
						self.environment.locals.insert(*symbol, data);
					}
					Statement::Alloc(symbol, value) => {
						let data = self.compute(value);
						let pointer = self.heap_generator.generate();
						self.heap.insert(pointer, data);
						self.environment.locals.insert(*symbol, Data::Heap(pointer));
					}
					Statement::Captures(symbol, values) =>
						if values.is_empty() {
							self.environment.locals.insert(*symbol, Data::None);
						} else {
							let data = Data::Captures(values.iter().map(|x| self.compute(x)).collect());
							let pointer = self.heap_generator.generate();
							self.heap.insert(pointer, data);
							self.environment.locals.insert(*symbol, Data::Heap(pointer));
						},
					Statement::Free(load) => self.free(self.load(load)),
					Statement::Call { symbol, result_repr: _, procedure, captures, argument } => {
						let Data::Procedure(id) = self.compute(procedure) else { panic!() };
						let captures = self.compute(captures);
						let argument = self.compute(argument);
						let environment =
							std::mem::replace(&mut self.environment, Environment::new(captures, argument, Some(id)));
						self.continuations.push((*symbol, environment, BlockId(current_block_id), i + 1));
						current_block_id = 0;
						current_index = 0;
						continue 'procedure;
					}
				}
			}

			match self.block(current_block_id).terminator.as_ref().unwrap() {
				Terminator::Abort => panic!(),
				Terminator::Return(operand) => {
					let data = self.compute(operand);
					if let Some(prototype) = self.prototype() {
						if !prototype.outer.is_empty() {
							self.free(self.environment.outer.clone());
						}
					}
					if let Some((symbol, environment, block, index)) = self.continuations.pop() {
						self.environment = environment;
						self.environment.locals.insert(symbol, data);
						current_block_id = block.0;
						current_index = index;
						continue 'procedure;
					} else {
						break 'procedure data;
					}
				}
				Terminator::Jump(BlockId(id), values) => {
					current_block_id = *id;
					for ((symbol, _), operand) in self.block(current_block_id).parameters.iter().zip(values.iter())
					{
						self.environment.locals.insert(*symbol, self.compute(operand));
					}
				}
				Terminator::Split(value, block_ids) => {
					let Data::Enum(k, v) = self.compute(value) else { panic!() };
					assert_eq!(k as usize, block_ids.len());
					current_block_id = block_ids[v as usize].0;
				}
				Terminator::CaseNat { index, limit, body, body_args, exit, exit_arg } => {
					let Data::Num(index) = self.compute(index) else { panic!() };
					let Data::Num(limit) = self.compute(limit) else { panic!() };
					if index < limit {
						current_block_id = body.0;
						let [x, y] = &*self.block(current_block_id).parameters else { panic!() };
						let x_data = self.compute(&body_args[0]);
						let y_data = self.compute(&body_args[1]);
						self.environment.locals.insert(x.0, x_data);
						self.environment.locals.insert(y.0, y_data);
					} else {
						current_block_id = exit.0;
						let [x] = &*self.block(current_block_id).parameters else { panic!() };
						let data = self.compute(exit_arg);
						self.environment.locals.insert(x.0, data);
					}
				}
			}

			current_index = 0;
		};
		data
	}

	fn free(&mut self, data: Data) {
		let Data::Heap(symbol) = data else { panic!() };
		let removed = self.heap.remove(&symbol);
		assert!(removed.is_some())
	}

	fn compute(&self, operand: &Value) -> Data {
		match operand {
			Value::None => Data::None,
			Value::Num(n) => Data::Num(*n),
			Value::Add(a, b) => {
				let Data::Num(n) = self.compute(a) else { panic!() };
				Data::Num(n.checked_add(*b).unwrap())
			}
			Value::Enum(k, v) => Data::Enum(*k, *v),
			Value::Procedure(n) => Data::Procedure(*n),
			Value::Load(load) => self.load(load),
			Value::Function { procedure, captures } => Data::Function {
				procedure: self.compute(procedure).into(),
				captures: self.compute(captures).into(),
			},
			Value::Array(inner) => Data::Array(inner.iter().map(|x| self.compute(x)).collect()),
			Value::Pair(left, right) => Data::Pair(self.compute(left).into(), self.compute(right).into()),
		}
	}

	fn load(&self, load: &Load) -> Data {
		let mut data = match load.register {
			Register::Outer(n) => match self.environment.outer {
				Data::Heap(ptr) => {
					let Data::Captures(captures) = &self.heap[&ptr] else { panic!() };
					captures[n.0].clone()
				}
				_ => panic!(),
			},
			Register::Parameter => self.environment.parameter.clone(),
			Register::Local(n) => self.environment.locals[&n].clone(),
		};
		for projector in &load.projectors {
			match projector {
				Projector::Exp(i, _) => {
					let Data::Array(v) = &data else { panic!() };
					data = v[*i as usize].clone();
				}
				Projector::Procedure => {
					let Data::Function { procedure, captures: _ } = &data else { panic!() };
					data = *procedure.clone();
				}
				Projector::Environment => {
					let Data::Function { procedure: _, captures } = &data else { panic!() };
					data = *captures.clone();
				}
				Projector::Field(field, _) => {
					let Data::Pair(left, right) = &data else { panic!() };
					data = match field {
						Field::Base => *left.clone(),
						Field::Fiber => *right.clone(),
					}
				}
				Projector::Bx(_) => {
					let Data::Heap(ptr) = &data else { panic!() };
					data = self.heap[ptr].clone()
				}
			}
		}
		data
	}
}

#[derive(Clone, Debug)]
pub enum Data {
	None,
	Heap(Symbol),
	Num(u64),
	Enum(u16, u8),
	Procedure(usize),
	Function { procedure: Box<Self>, captures: Box<Self> },
	Captures(Box<[Self]>),
	Array(Box<[Self]>),
	Pair(Box<Self>, Box<Self>),
}
