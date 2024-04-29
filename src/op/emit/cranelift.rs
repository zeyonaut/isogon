use std::collections::HashMap;

use cranelift::{
	codegen::{
		ir::{
			types::{I16, I32, I64, I8},
			AbiParam, Block, BlockCall, ExtFuncData, ExternalName, FuncRef, Function, InstBuilder,
			InstBuilderBase as _, JumpTableData, MemFlags, Signature, StackSlot, StackSlotData, StackSlotKind,
			TrapCode, Type, UserExternalName, UserFuncName, Value,
		},
		isa::{CallConv, TargetFrontendConfig},
		settings, verifier,
	},
	frontend::{FunctionBuilder, FunctionBuilderContext},
};

use crate::{
	common::{Field, Symbol},
	ir::linear,
};

pub fn emit_cranelift(program: &linear::Program) -> EmittedProgram {
	let flags = settings::Flags::new(settings::builder());
	let entry = Emitter::build(
		MAIN_NAME,
		&linear::Prototype { outer: Vec::new(), parameter: (None, None), result: program.repr.clone() },
		&program.entry,
		&program.procedures,
	);
	verifier::verify_function(&entry, &flags).unwrap();
	let mut functions = Vec::new();
	for (i, (prototype, procedure)) in program.procedures.iter().enumerate() {
		let function = Emitter::build(
			UserExternalName { namespace: USER_NAMESPACE, index: i as u32 },
			prototype,
			procedure,
			&program.procedures,
		);
		verifier::verify_function(&function, &flags).unwrap();
		functions.push(function);
	}
	EmittedProgram { entry, functions }
}

pub struct EmittedProgram {
	pub entry: Function,
	pub functions: Vec<Function>,
}

const MAIN_NAME: UserExternalName = UserExternalName { namespace: 0, index: 0 };
const USER_NAMESPACE: u32 = 1;
const EXT_NAMESPACE: u32 = 2;
const MALLOC_NAME: UserExternalName = UserExternalName { namespace: EXT_NAMESPACE, index: 0 };
const FREE_NAME: UserExternalName = UserExternalName { namespace: EXT_NAMESPACE, index: 1 };

const POINTER_TYPE: Type = I64;
const OVERSIZED_TYPE: Type = POINTER_TYPE;

const CALL_CONV: CallConv = CallConv::WindowsFastcall;

struct Emitter<'a, 'b> {
	builder: &'a mut FunctionBuilder<'b>,
	parameter: Option<Predata>,
	environment: Option<Predata>,
	environment_offset_layouts: Vec<Option<(i32, DataLayout)>>,
	blocks_to_parameter_slots: Vec<Vec<Option<StackSlot>>>,
	locals: HashMap<Symbol, Option<Predata>>,
	result: Option<ResultKind>,
	func_refs: Vec<FuncRef>,
	func_ref_free: FuncRef,
	func_ref_malloc: FuncRef,
	blocks: Vec<Block>,
}

#[derive(Clone, Copy)]
enum ResultKind {
	Direct,
	Indirect(Value),
}

impl<'a, 'b> Emitter<'a, 'b> {
	fn build(
		name: UserExternalName,
		prototype: &linear::Prototype,
		procedure: &linear::Procedure,
		procedures: &[(linear::Prototype, linear::Procedure)],
	) -> Function {
		// TODO: Reorganize.
		let (signature, signature_flags) = emit_signature(prototype);
		let mut function = Function::with_name_signature(UserFuncName::User(name), signature);
		let free_name = function.declare_imported_user_function(FREE_NAME);
		let malloc_name = function.declare_imported_user_function(MALLOC_NAME);

		let mut procedure_names = Vec::new();
		for i in 0..procedures.len() {
			procedure_names.push(
				function.declare_imported_user_function(UserExternalName {
					namespace: USER_NAMESPACE,
					index: i as u32,
				}),
			)
		}
		// TODO: Declare other procedures here.

		let mut ctx = FunctionBuilderContext::new();
		let mut builder = FunctionBuilder::new(&mut function, &mut ctx);
		let blocks = (0..procedure.blocks.len()).map(|_| builder.create_block()).collect::<Vec<_>>();
		let entry = *(blocks.first().unwrap());
		builder.append_block_params_for_function_params(entry);

		let mut emitter = {
			let mut free_signature = Signature::new(CALL_CONV);
			free_signature.params.push(AbiParam::new(I64));
			let free_sigref = builder.import_signature(free_signature);
			let func_ref_free = builder.import_function(ExtFuncData {
				name: ExternalName::user(free_name),
				signature: free_sigref,
				colocated: false,
			});

			let mut malloc_signature = Signature::new(CALL_CONV);
			malloc_signature.params.push(AbiParam::new(I64));
			malloc_signature.returns.push(AbiParam::new(I64));
			let malloc_sigref = builder.import_signature(malloc_signature);
			let func_ref_malloc = builder.import_function(ExtFuncData {
				name: ExternalName::user(malloc_name),
				signature: malloc_sigref,
				colocated: false,
			});

			let mut func_refs = Vec::new();
			for (procedure_name, (prototype, _)) in procedure_names.iter().zip(procedures) {
				let (signature, _) = emit_signature(prototype);
				let sigref = builder.import_signature(signature);
				func_refs.push(builder.import_function(ExtFuncData {
					name: ExternalName::user(*procedure_name),
					signature: sigref,
					colocated: true,
				}));
			}

			let parameters = builder.block_params(entry);
			let environment =
				(!signature_flags.is_environment_erased).then(|| Predata::Direct(parameters[0], DataLayout::I64));
			let mut environment_offset_layouts = Vec::new();
			{
				let mut environment_layout = DataLayout::I0;
				for (_, layout) in &prototype.outer {
					environment_offset_layouts.push(layout.as_ref().map(|layout| {
						let layout = DataLayout::from(layout);
						let offset = environment_layout.next_offset(layout);
						let result = (offset as i32, layout);
						environment_layout = environment_layout.pair(layout);
						result
					}))
				}
			}

			let parameter = (!signature_flags.is_parameter_erased).then(|| {
				if signature_flags.is_parameter_oversized {
					Predata::Indirect(parameters[1], 0, prototype.parameter.1.as_ref().unwrap().into())
				} else {
					Predata::Direct(parameters[1], prototype.parameter.1.as_ref().unwrap().into())
				}
			});
			let result = (!signature_flags.is_result_erased).then(|| {
				if signature_flags.is_result_oversized {
					ResultKind::Indirect(parameters[1 + (!signature_flags.is_parameter_erased as usize)])
				} else {
					ResultKind::Direct
				}
			});
			Emitter {
				builder: &mut builder,
				environment,
				environment_offset_layouts,
				parameter,
				locals: HashMap::new(),
				result,
				blocks,
				blocks_to_parameter_slots: Vec::new(),
				func_ref_free,
				func_ref_malloc,
				func_refs,
			}
		};

		emitter.preprocess_blocks(&procedure.blocks);
		emitter.build_blocks(&procedure.blocks);

		builder.seal_all_blocks();
		builder.finalize();
		function
	}

	fn preprocess_blocks(&mut self, preblocks: &[linear::Block]) {
		for (block, preblock) in self.blocks.clone().into_iter().zip(preblocks) {
			self.builder.switch_to_block(block);
			let mut parameter_slots = Vec::new();
			for (symbol, layout) in preblock.parameters.iter() {
				let emitted_register = if let Some(layout) = layout {
					let layout = DataLayout::from(layout);
					if let Some(ty) = layout.ty() {
						self.builder.append_block_param(block, ty);
						parameter_slots.push(None);
						Some(Predata::Direct(*self.builder.block_params(block).last().unwrap(), layout))
					} else {
						let slot = self.create_slot(layout);
						parameter_slots.push(Some(slot));
						Some(Predata::StackSlot(slot, 0, layout))
					}
				} else {
					parameter_slots.push(None);
					None
				};
				self.locals.insert(*symbol, emitted_register);
			}
			self.blocks_to_parameter_slots.push(parameter_slots);
		}
	}

	fn build_blocks(&mut self, preblocks: &[linear::Block]) {
		for (block, preblock) in self.blocks.clone().into_iter().zip(preblocks) {
			self.builder.switch_to_block(block);
			for statement in &preblock.statements {
				self.emit_statement(statement);
			}
			self.emit_terminator(preblock.terminator.as_ref().unwrap());
		}
	}

	fn emit_statement(&mut self, statement: &linear::Statement) {
		match statement {
			linear::Statement::Assign(symbol, value) => {
				let predata = self.predata(value);
				self.assign(*symbol, predata);
			}
			linear::Statement::Alloc(symbol, value) => {
				let predata = self.predata(value);
				let pointer = predata.map(|predata| {
					let size = self.builder.ins().iconst(I64, predata.layout().size as i64);
					let malloc_inst = self.builder.ins().call(self.func_ref_malloc, &[size]);
					let results = self.builder.inst_results(malloc_inst);
					assert_eq!(results.len(), 1);
					let pointer = results[0];
					self.store(pointer, predata);
					Predata::Direct(pointer, DataLayout::I64)
				});
				self.assign(*symbol, pointer)
			}
			linear::Statement::Captures(symbol, values) => {
				let predatas = values.iter().map(|value| self.predata(value)).collect::<Vec<_>>();
				let mut layout = DataLayout::I0;
				let mut offsets = Vec::new();
				for predata in &predatas {
					if let Some(predata) = predata.as_ref() {
						offsets.push(Some(layout.next_offset(predata.layout())));
						layout = layout.pair(predata.layout());
					} else {
						offsets.push(None);
					}
				}
				let pointer = if layout.size == 0 {
					None
				} else {
					let size = self.builder.ins().iconst(I64, layout.size as i64);
					let malloc_inst = self.builder.ins().call(self.func_ref_malloc, &[size]);
					let results = self.builder.inst_results(malloc_inst);
					assert_eq!(results.len(), 1);
					let pointer = results[0];
					for (i, predata) in predatas.into_iter().enumerate() {
						if let Some(predata) = predata {
							let pointer = if i == 0 {
								pointer
							} else {
								self.builder.ins().iadd_imm(pointer, offsets[i].unwrap() as i64)
							};
							self.store(pointer, predata);
						}
					}
					Some(Predata::Direct(pointer, DataLayout::I64))
				};
				self.assign(*symbol, pointer)
			}
			linear::Statement::Free(pointer) => {
				let pointer = self.emit_load(pointer).unwrap();
				let pointer = self.value(pointer);
				self.builder.ins().call(self.func_ref_free, &[pointer]);
			}
			linear::Statement::Call { symbol, result_repr, procedure, captures, argument } => {
				let callee = self.predata(procedure).unwrap();
				let environment = self.predata(captures);
				let argument = self.predata(argument);
				let result = result_repr.as_ref().map(DataLayout::from);
				self.call(*symbol, callee, environment, argument, result);
			}
		}
	}

	fn emit_terminator(&mut self, terminator: &linear::Terminator) {
		match terminator {
			linear::Terminator::Abort => {
				self.builder.ins().trap(TrapCode::UnreachableCodeReached);
			}
			linear::Terminator::Return(argument) => {
				let argument = self.predata(argument);
				if let Some(argument) = argument {
					match self.result.unwrap() {
						ResultKind::Direct => {
							let value = self.value(argument);
							if let Some(pointer) = self.environment {
								let pointer = self.value(pointer);
								self.builder.ins().call(self.func_ref_free, &[pointer]);
							}
							self.builder.ins().return_(&[value]);
						}
						ResultKind::Indirect(dest) => {
							// NOTE: The result kind can only be indirect if the return value cannot be direct.
							let Data::Indirect(src, layout) = self.data(argument) else { panic!() };
							self.copy_memory(dest, src, layout);
							if let Some(pointer) = self.environment {
								let pointer = self.value(pointer);
								self.builder.ins().call(self.func_ref_free, &[pointer]);
							}
							self.builder.ins().return_(&[]);
						}
					}
				} else {
					assert!(self.result.is_none());
					self.builder.ins().return_(&[]);
				}
			}
			linear::Terminator::Jump(block, arguments) => {
				let mut processed_arguments = Vec::new();
				for (i, argument) in arguments.iter().enumerate() {
					let predata = self.predata(argument);
					if let Some(slot) = self.blocks_to_parameter_slots[block.0][i] {
						let data = self.data(predata.unwrap());
						self.store_data_in_slot(slot, 0, data);
					} else if let Some(value) = predata {
						processed_arguments.push(self.value(value));
					}
				}
				self.builder.ins().jump(self.blocks[block.0], &processed_arguments);
			}
			linear::Terminator::Split(scrutinee, blocks) => {
				assert!(blocks.len() > 1);
				let block_calls = blocks
					.iter()
					.map(|block| {
						BlockCall::new(
							self.blocks[block.0],
							&[],
							&mut self.builder.ins().data_flow_graph_mut().value_lists,
						)
					})
					.collect::<Vec<_>>();
				let jump_table =
					self.builder.create_jump_table(JumpTableData::new(*block_calls.last().unwrap(), &block_calls));
				// NOTE: Even if 0 and 1 were erased, we require that splits are greater than 1.
				let predata = self.predata(scrutinee).unwrap();
				let data = self.value(predata);
				let data = self.builder.ins().uextend(I32, data);
				self.builder.ins().br_table(data, jump_table);
			}
			linear::Terminator::CaseNat { index, limit, body, body_args, exit, exit_arg } => {
				let index = self.predata(index).unwrap();
				let index = self.value(index);
				let limit = self.predata(limit).unwrap();
				let limit = self.value(limit);
				let condition = self.builder.ins().isub(limit, index);
				if self.blocks_to_parameter_slots[exit.0][0].is_none() {
					// Accumulator is small; we can do a simple branch.
					let body_args = body_args.each_ref().map(|x| {
						let x = self.predata(x).unwrap();
						self.value(x)
					});
					let exit_arg = self.predata(exit_arg).unwrap();
					let exit_arg = self.value(exit_arg);
					self.builder.ins().brif(
						condition,
						self.blocks[exit.0],
						&[exit_arg],
						self.blocks[body.0],
						&body_args,
					);
				} else {
					// Accumulator is oversized; we need to generate extra blocks after the branch.
					let next_index = self.predata(&body_args[0]).unwrap();
					let next_index = self.value(next_index);
					let body_prelude = self.builder.create_block();
					self.builder.append_block_param(body_prelude, I64);
					let exit_prelude = self.builder.create_block();
					self.builder.ins().brif(condition, exit_prelude, &[], body_prelude, &[next_index]);

					// Generate body prelude.
					self.builder.switch_to_block(body_prelude);
					let body_prelude_args = self.builder.block_params(body_prelude).to_vec();
					let body_accumulator_slot = self.blocks_to_parameter_slots[body.0][1].unwrap();
					// NOTE: Stack slots should never be zero-sized.
					let body_accumulator_data = self.predata(&body_args[0]).unwrap();
					let body_accumulator_data = self.data(body_accumulator_data);
					self.store_data_in_slot(body_accumulator_slot, 0, body_accumulator_data);
					let body_block = self.blocks[body.0];
					self.builder.ins().jump(body_block, &body_prelude_args);

					// Generate exit prelude.
					self.builder.switch_to_block(exit_prelude);
					let exit_accumulator_slot = self.blocks_to_parameter_slots[exit.0][0].unwrap();
					let exit_accumulator_data = self.predata(&exit_arg).unwrap();
					let exit_accumulator_data = self.data(exit_accumulator_data);
					self.store_data_in_slot(exit_accumulator_slot, 0, exit_accumulator_data);
					let exit_block = self.blocks[exit.0];
					self.builder.ins().jump(exit_block, &[]);
				}
			}
		}
	}

	fn assign(&mut self, symbol: Symbol, predata: Option<Predata>) { self.locals.insert(symbol, predata); }

	fn store(&mut self, dest: Value, src: Predata) {
		let layout = src.layout();
		let ty = layout.ty();
		if ty.is_some() {
			let value = self.value(src);
			self.builder.ins().store(
				if layout.size == layout.align as _ {
					MemFlags::trusted()
				} else {
					MemFlags::new().with_notrap()
				},
				value,
				dest,
				0,
			);
		} else {
			let Data::Indirect(src, _) = self.data(src) else { panic!() };
			self.copy_memory(dest, src, layout);
		}
	}

	fn call(
		&mut self,
		symbol: Symbol,
		callee: Predata,
		environment: Option<Predata>,
		argument: Option<Predata>,
		result: Option<DataLayout>,
	) {
		let mut arguments = Vec::new();
		let mut signature_params = Vec::new();
		let mut signature_returns = Vec::new();
		arguments.push(if let Some(environment) = environment {
			self.value(environment)
		} else {
			self.builder.ins().iconst(I64, 0)
		});
		signature_params.push(AbiParam::new(I64));
		if let Some(argument) = argument {
			let data = self.data(argument);
			arguments.push(data.value());
			signature_params.push(AbiParam::new(data.ty()));
		}
		if let Some(layout) = result {
			if let Some(ty) = layout.ty() {
				signature_returns.push(AbiParam::new(ty));
			} else {
				let slot = self.create_slot(layout);
				arguments.push(self.data(Predata::StackSlot(slot, 0, layout)).value());
				signature_params.push(AbiParam::new(I64));
				self.assign(symbol, Some(Predata::StackSlot(slot, 0, layout)));
			}
		}
		let call_inst = 'inst: {
			let callee = match callee {
				Predata::FuncRef(func_ref) => {
					break 'inst self.builder.ins().call(func_ref, &arguments);
				}
				Predata::Direct(value, _) => value,
				Predata::Indirect(address, offset, layout) => self.builder.ins().load(
					layout.ty().unwrap(),
					if layout.size == layout.align as _ {
						MemFlags::trusted()
					} else {
						MemFlags::new().with_notrap()
					},
					address,
					offset,
				),
				Predata::StackSlot(slot, offset, layout) =>
					self.builder.ins().stack_load(layout.ty().unwrap(), slot, offset),
			};
			let mut signature = Signature::new(CALL_CONV);
			signature.params.extend(signature_params);
			signature.returns.extend(signature_returns);
			let signature_ref = self.builder.import_signature(signature);
			self.builder.ins().call_indirect(signature_ref, callee, &arguments)
		};
		if let Some(layout) = result {
			if layout.ty().is_some() {
				let results = self.builder.inst_results(call_inst);
				assert_eq!(results.len(), 1);
				self.assign(symbol, Some(Predata::Direct(results[0], layout)))
			}
		}
	}

	fn predata(&mut self, value: &linear::Value) -> Option<Predata> {
		Some(match value {
			linear::Value::None => return None,
			linear::Value::Num(n) => Predata::Direct(self.builder.ins().iconst(I64, *n as i64), DataLayout::I64),
			linear::Value::Add(a, b) => {
				let a = self.predata(a).unwrap();
				let a = self.value(a);
				let b = self.builder.ins().iconst(I64, *b as i64);
				Predata::Direct(
					self.builder.ins().uadd_overflow_trap(a, b, TrapCode::IntegerOverflow),
					DataLayout::I64,
				)
			}
			linear::Value::Enum(_, n) =>
				Predata::Direct(self.builder.ins().iconst(I8, *n as i64), DataLayout::I8),
			linear::Value::Procedure(n) => Predata::FuncRef(self.func_refs[*n]),
			linear::Value::Load(load) => self.emit_load(load)?,
			linear::Value::Function { procedure, captures } => {
				let layout = DataLayout::FUNCTION;
				let slot = self.create_slot(layout);
				let procedure = self.predata(procedure).unwrap();
				let procedure = self.value(procedure);
				self.builder.ins().stack_store(procedure, slot, 0);
				if let Some(captures) = self.predata(captures) {
					let captures = self.value(captures);
					self.builder.ins().stack_store(captures, slot, 8);
				}
				Predata::StackSlot(slot, 0, layout)
			}
			linear::Value::Array(values) => {
				let predatas = values.iter().map(|x| self.predata(x)).collect::<Vec<_>>();
				// NOTE: This short-circuits if the array is empty.
				let first_predata = predatas.first().copied().flatten()?;
				let sublayout = first_predata.layout();
				let layout = sublayout.pow(predatas.len().try_into().unwrap());
				let sublayout_stride = sublayout.stride();
				match layout.ty() {
					Some(ty) => {
						let sublayout_ty = sublayout.ty().unwrap();
						let value = self.value(first_predata);
						let mut value =
							if ty != sublayout_ty { self.builder.ins().uextend(ty, value) } else { value };
						for (i, predata) in predatas.iter().copied().enumerate().skip(1) {
							let data = self.value(predata.unwrap());
							let data = if ty != sublayout_ty { self.builder.ins().uextend(ty, data) } else { data };
							let data = self
								.builder
								.ins()
								.ishl_imm(data, (u32::try_from(i).unwrap() * sublayout_stride) as i64);
							value = self.builder.ins().band(value, data);
						}
						Predata::Direct(value, layout)
					}
					None => {
						let slot = self.create_slot(layout);
						for (i, value) in predatas.into_iter().enumerate() {
							let v = self.data(value.unwrap());
							self.store_data_in_slot(
								slot,
								(u32::try_from(i).unwrap() * sublayout_stride).try_into().unwrap(),
								v,
							);
						}
						Predata::StackSlot(slot, 0, layout)
					}
				}
			}
			linear::Value::Pair(a, b) => {
				let a = self.predata(a);
				let b = self.predata(b);
				match (a, b) {
					(None, None) => return None,
					(Some(a), None) => a,
					(None, Some(b)) => b,
					(Some(a), Some(b)) => {
						let a_layout = a.layout();
						let b_layout = b.layout();
						let b_offset = a_layout.next_offset(b_layout);
						let layout = a_layout.pair(b_layout);
						match layout.ty() {
							Some(ty) => {
								let a = self.value(a);
								let a =
									if ty != a_layout.ty().unwrap() { self.builder.ins().uextend(ty, a) } else { a };
								let b = self.value(b);
								let b =
									if ty != b_layout.ty().unwrap() { self.builder.ins().uextend(ty, b) } else { b };
								let b =
									if b_offset > 0 { self.builder.ins().ishl_imm(b, b_offset as i64) } else { b };
								let value = self.builder.ins().band(a, b);
								Predata::Direct(value, layout)
							}
							None => {
								let slot = self.create_slot(layout);
								let a = self.data(a);
								self.store_data_in_slot(slot, 0, a);
								let b = self.data(b);
								self.store_data_in_slot(slot, b_offset.try_into().unwrap(), b);
								Predata::StackSlot(slot, 0, layout)
							}
						}
					}
				}
			}
		})
	}

	fn emit_load(&mut self, load: &linear::Load) -> Option<Predata> {
		let mut predata = match load.register {
			linear::Register::Outer(n) => {
				let (offset, layout) = self.environment_offset_layouts[n.0]?;
				let environment = self.value(self.environment.unwrap());
				Predata::Indirect(environment, offset, layout)
			}
			linear::Register::Parameter => self.parameter?,
			linear::Register::Local(n) => self.locals[&n]?,
		};
		for modifier in &load.projectors {
			predata = match modifier {
				linear::Projector::Exp(n, layout) => {
					let layout = DataLayout::from(layout.as_ref()?);
					let additional_offset = (layout.stride() * *n as u32) as i32;
					match predata {
						Predata::FuncRef(_) => panic!(),
						Predata::Direct(value, _) =>
							Predata::Direct(self.builder.ins().ushr_imm(value, additional_offset as i64), layout),
						Predata::Indirect(address, offset, _) =>
							Predata::Indirect(address, offset + additional_offset, layout),
						Predata::StackSlot(slot, offset, _) =>
							Predata::StackSlot(slot, offset + additional_offset, layout),
					}
				}
				linear::Projector::Procedure => match predata {
					Predata::FuncRef(_) | Predata::Direct(_, _) => panic!("functions should be oversized"),
					Predata::Indirect(address, offset, _) => Predata::Indirect(address, offset, DataLayout::I64),
					Predata::StackSlot(slot, offset, _) => Predata::StackSlot(slot, offset, DataLayout::I64),
				},
				linear::Projector::Environment => match predata {
					Predata::FuncRef(_) | Predata::Direct(_, _) => panic!("functions should be oversized"),
					Predata::Indirect(address, offset, _) =>
						Predata::Indirect(address, offset + 8, DataLayout::I64),
					Predata::StackSlot(slot, offset, _) => Predata::StackSlot(slot, offset + 8, DataLayout::I64),
				},
				linear::Projector::Field(field, [base, fiber]) => match (base, fiber) {
					(None, None) => None?,
					(None, Some(_)) => (field == &Field::Fiber).then_some(predata)?,
					(Some(_), None) => (field == &Field::Base).then_some(predata)?,
					(Some(base), Some(fiber)) => {
						let (layout, additional_offset) = match field {
							Field::Base => (DataLayout::from(base), 0),
							Field::Fiber => {
								let fiber = fiber.into();
								(fiber, DataLayout::from(base).next_offset(fiber) as i32)
							}
						};
						match predata {
							Predata::FuncRef(_) => panic!(),
							Predata::Direct(value, _) =>
								Predata::Direct(self.builder.ins().ushr_imm(value, additional_offset as i64), layout),
							Predata::Indirect(address, offset, _) =>
								Predata::Indirect(address, offset + additional_offset, layout),
							Predata::StackSlot(slot, offset, _) =>
								Predata::StackSlot(slot, offset + additional_offset, layout),
						}
					}
				},
				linear::Projector::Bx(layout) => {
					let address = self.value(predata);
					let layout = DataLayout::from(layout.as_ref()?);
					match layout.ty() {
						Some(ty) =>
							Predata::Direct(self.builder.ins().load(ty, MemFlags::trusted(), address, 0), layout),
						None => Predata::Indirect(address, 0, layout),
					}
				}
			}
		}
		Some(predata)
	}

	fn store_data_in_slot(&mut self, slot: StackSlot, offset: i32, data: Data) {
		match data {
			Data::Direct(value, layout) => match layout.size {
				1 | 2 | 4 | 8 => {
					self.builder.ins().stack_store(value, slot, offset);
				}
				3 => {
					let (lower, upper) = self.builder.ins().isplit(value);
					self.builder.ins().stack_store(lower, slot, offset);
					let (lower, _) = self.builder.ins().isplit(upper);
					self.builder.ins().stack_store(lower, slot, offset + 2);
				}
				5 => {
					let (lower, upper) = self.builder.ins().isplit(value);
					self.builder.ins().stack_store(lower, slot, offset);
					let (lower, _) = self.builder.ins().isplit(upper);
					let (lower, _) = self.builder.ins().isplit(lower);
					self.builder.ins().stack_store(lower, slot, offset + 4);
				}
				6 => {
					let (lower, upper) = self.builder.ins().isplit(value);
					self.builder.ins().stack_store(lower, slot, offset);
					let (lower, _) = self.builder.ins().isplit(upper);
					self.builder.ins().stack_store(lower, slot, offset + 4);
				}
				7 => {
					let (lower, upper) = self.builder.ins().isplit(value);
					self.builder.ins().stack_store(lower, slot, offset);
					let (lower, upper) = self.builder.ins().isplit(upper);
					self.builder.ins().stack_store(lower, slot, offset + 4);
					let (lower, _) = self.builder.ins().isplit(upper);
					self.builder.ins().stack_store(lower, slot, offset + 6);
				}
				_ => unimplemented!(),
			},
			Data::Indirect(src, layout) => {
				let dest = self.builder.ins().stack_addr(I64, slot, offset);
				self.copy_memory(dest, src, layout);
			}
		}
	}

	fn copy_memory(&mut self, dest: Value, src: Value, layout: DataLayout) {
		self.builder.emit_small_memory_copy(
			TargetFrontendConfig {
				default_call_conv: CALL_CONV,
				pointer_width: target_lexicon::PointerWidth::U64,
			},
			dest,
			src,
			layout.size as u64,
			1,
			layout.align,
			true,
			MemFlags::trusted(),
		)
	}

	/// Create a stack slot with the specified layout.
	fn create_slot(&mut self, layout: DataLayout) -> StackSlot {
		self.builder.create_sized_stack_slot(StackSlotData::new(StackSlotKind::ExplicitSlot, layout.size))
	}

	// Either direct address with a register type, or indirect with a layout.
	fn data(&mut self, prevalue: Predata) -> Data {
		match prevalue {
			Predata::FuncRef(func_ref) =>
				Data::Direct(self.builder.ins().func_addr(I64, func_ref), DataLayout::I64),
			Predata::Direct(value, layout) => Data::Direct(value, layout),
			Predata::Indirect(address, offset, layout) =>
				Data::Indirect(self.builder.ins().iadd_imm(address, offset as i64), layout),
			Predata::StackSlot(slot, offset, layout) =>
				Data::Indirect(self.builder.ins().stack_addr(I64, slot, offset), layout),
		}
	}

	fn value(&mut self, predata: Predata) -> Value {
		match predata {
			Predata::FuncRef(func_ref) => self.builder.ins().func_addr(I64, func_ref),
			Predata::Direct(value, _) => value,
			Predata::Indirect(address, offset, layout) => self.builder.ins().load(
				layout.ty().unwrap(),
				if layout.size == layout.align as _ {
					MemFlags::trusted()
				} else {
					MemFlags::new().with_notrap()
				},
				address,
				offset,
			),
			Predata::StackSlot(slot, offset, layout) =>
				self.builder.ins().stack_load(layout.ty().unwrap(), slot, offset),
		}
	}
}

#[derive(Clone, Copy)]
enum Data {
	Direct(Value, DataLayout),
	Indirect(Value, DataLayout),
}

impl Data {
	fn value(self) -> Value {
		match self {
			Self::Direct(value, _) => value,
			Self::Indirect(value, _) => value,
		}
	}

	fn ty(self) -> Type {
		match self {
			Self::Direct(_, layout) => layout.ty().unwrap(),
			Self::Indirect(_, _) => I64,
		}
	}

	fn layout(self) -> DataLayout {
		match self {
			Self::Direct(_, layout) => layout,
			Self::Indirect(_, layout) => layout,
		}
	}
}

#[derive(Clone, Copy)]
enum Predata {
	FuncRef(FuncRef),
	Direct(Value, DataLayout),
	Indirect(Value, i32, DataLayout),
	StackSlot(StackSlot, i32, DataLayout),
}

impl Predata {
	fn layout(self) -> DataLayout {
		match self {
			Self::FuncRef(_) => DataLayout::I64,
			Self::Direct(_, layout) => layout,
			Self::Indirect(_, _, layout) => layout,
			Self::StackSlot(_, _, layout) => layout,
		}
	}
}

struct SignatureFlags {
	is_environment_erased: bool,
	is_parameter_erased: bool,
	is_parameter_oversized: bool,
	is_result_erased: bool,
	is_result_oversized: bool,
}

#[derive(Clone, Copy)]
struct DataLayout {
	size: u32,
	align: u8,
}

impl DataLayout {
	const I0: Self = Self::new(0, 0);
	const I8: Self = Self::new(1, 1);
	const I64: Self = Self::new(8, 8);
	const FUNCTION: Self = Self::new(8 * 2, 8);

	const fn new(size: u32, alignment: u8) -> Self { Self { size, align: alignment } }
	/// The smallest integer type, if it exists, of a register capable of storing this layout.
	fn ty(self) -> Option<Type> {
		Some(if self.size == 1 {
			I8
		} else if self.size == 2 {
			I16
		} else if self.size <= 4 {
			I32
		} else if self.size <= 8 {
			I64
		} else {
			return None;
		})
	}

	fn pair(self, other: Self) -> Self {
		Self { size: self.next_offset(other) + other.size, align: self.align.max(other.align) }
	}

	fn next_offset(self, other: Self) -> u32 { self.size.next_multiple_of(other.align as _) }

	fn stride(self) -> u32 { self.next_offset(self) }

	fn pow(self, n: u32) -> Self {
		match n {
			0 => unimplemented!(),
			n => Self { size: self.stride() * (n - 1), align: self.align }.pair(self),
		}
	}
}

impl From<&linear::Layout> for DataLayout {
	fn from(value: &linear::Layout) -> Self {
		match value {
			linear::Layout::Byte => Self { size: 1, align: 1 },
			linear::Layout::Nat => Self { size: 8, align: 8 },
			linear::Layout::Ptr => Self { size: 8, align: 8 },
			linear::Layout::Fun => Self { size: 8 * 2, align: 8 },
			linear::Layout::Pair(pair) => Self::from(&pair[0]).pair((&pair[1]).into()),
			linear::Layout::Array(n, layout) => {
				let layout = Self::from(layout.as_ref());
				layout.pow(n.0.try_into().unwrap())
			}
		}
	}
}

fn emit_signature(prototype: &linear::Prototype) -> (Signature, SignatureFlags) {
	let parameter_ty = prototype.parameter.1.as_ref().map(|x| DataLayout::from(x).ty());
	let is_environment_erased = prototype.outer.iter().map(|(_, layout)| layout).all(|x| x.is_none());
	let result_ty = prototype.result.as_ref().map(|x| DataLayout::from(x).ty());

	let mut signature = Signature::new(CALL_CONV);
	// Environment.
	signature.params.push(AbiParam::new(POINTER_TYPE));

	// TODO: Reorganize.
	let mut is_parameter_oversized = false;
	if let Some(ty) = parameter_ty {
		signature.params.push(AbiParam::new(if let Some(ty) = ty {
			ty
		} else {
			is_parameter_oversized = true;
			POINTER_TYPE
		}));
	}
	let mut is_result_oversized = false;
	if let Some(ty) = result_ty {
		if let Some(ty) = ty {
			signature.returns.push(AbiParam::new(ty));
		} else {
			is_result_oversized = true;
			signature.params.push(AbiParam::new(POINTER_TYPE));
		};
	}

	(
		signature,
		SignatureFlags {
			is_environment_erased,
			is_parameter_erased: parameter_ty.is_none(),
			is_parameter_oversized,
			is_result_erased: result_ty.is_none(),
			is_result_oversized,
		},
	)
}
