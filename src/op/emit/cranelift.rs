use std::collections::HashMap;

use cranelift::{
	codegen::{
		ir::{
			types::{I16, I32, I64, I8},
			AbiParam, Block, BlockCall, FuncRef, Function, InstBuilder, InstBuilderBase as _, JumpTableData,
			MemFlags, Signature, StackSlot, StackSlotData, StackSlotKind, TrapCode, Type, UserExternalName,
			UserFuncName, Value, ValueListPool,
		},
		isa::{CallConv, TargetFrontendConfig},
	},
	frontend::{FunctionBuilder, FunctionBuilderContext},
};

use crate::{
	common::{Field, Symbol},
	ir::linear,
};

pub fn emit_cranelift(_program: &linear::Program) {
	todo!();
}

const MAIN_NAME: UserExternalName = UserExternalName { namespace: 0, index: 0 };
const USER_NAMESPACE: u32 = 1;
const EXT_NAMESPACE: u32 = 2;
const MALLOC_NAME: UserExternalName = UserExternalName { namespace: EXT_NAMESPACE, index: 0 };
const FREE_NAME: UserExternalName = UserExternalName { namespace: EXT_NAMESPACE, index: 1 };

const POINTER_TYPE: Type = I64;
const OVERSIZED_TYPE: Type = POINTER_TYPE;

const CALL_CONV: CallConv = CallConv::WindowsFastcall;

fn emit_function(
	name: UserExternalName,
	prototype: &linear::Prototype,
	procedure: &linear::Procedure,
) -> Function {
	let (signature, signature_flags) = emit_signature(prototype);
	let mut function = Function::with_name_signature(UserFuncName::User(name), signature);
	let mut ctx = FunctionBuilderContext::new();
	let mut function_builder = FunctionBuilder::new(&mut function, &mut ctx);
	let blocks = (0..procedure.blocks.len()).map(|_| function_builder.create_block()).collect::<Box<_>>();
	let entry = *(blocks.first().unwrap());
	function_builder.append_block_params_for_function_params(entry);
	let mut emitter = Emitter::new(&mut function_builder, signature_flags, entry);
	for (block, preblock) in blocks.iter().copied().zip(&procedure.blocks) {
		emitter.process_parameters(block, preblock);
	}
	for (block, preblock) in blocks.iter().copied().zip(&procedure.blocks) {
		emitter.build(block, preblock);
	}
	function_builder.seal_all_blocks();
	function_builder.finalize();
	function
}

struct Emitter<'a, 'b> {
	builder: &'a mut FunctionBuilder<'b>,
	parameter: Option<Predata>,
	snapshot: Option<Predata>,
	outer: Vec<Option<Predata>>,
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
	fn new(builder: &'a mut FunctionBuilder<'b>, flags: SignatureFlags, entry: Block) -> Self {
		let parameters = builder.block_params(entry);
		Self {
			parameter: todo!(), // (!flags.is_parameter_erased).then(|| parameters[0]),
			snapshot: todo!(),
			outer: todo!(), // (!flags.is_snapshot_erased).then(|| parameters[!flags.is_parameter_erased as usize]),
			locals: HashMap::new(),
			result: todo!(),
			builder,
			func_refs: Vec::new(),
			blocks: todo!(),
			func_ref_free: todo!(),
			func_ref_malloc: todo!(),
		}
	}

	fn process_parameters(&mut self, block: Block, preblock: &linear::Block) {
		self.builder.switch_to_block(block);

		for (symbol, layout) in preblock.parameters.iter() {
			let emitted_register = if let Some(layout) = layout {
				let layout = DataLayout::from(layout);
				if let Some(ty) = layout.ty() {
					self.builder.append_block_param(block, ty);
					Some(Predata::Direct(*self.builder.block_params(block).last().unwrap(), layout))
				} else {
					let slot = self.create_slot(layout);
					Some(Predata::StackSlot(slot, 0, layout))
				}
			} else {
				None
			};
			self.locals.insert(*symbol, emitted_register);
		}
	}

	fn assign(&mut self, symbol: Symbol, predata: Option<Predata>) {
		todo!();
	}

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

	fn build(&mut self, block: Block, preblock: &linear::Block) {
		self.builder.switch_to_block(block);

		for statement in &preblock.statements {
			match statement {
				linear::Statement::Assign(symbol, value) => {
					let predata = self.predata(value);
					self.assign(*symbol, predata);
				}
				linear::Statement::Alloc(symbol, value) => {
					let predata = self.predata(value);
					let pointer = predata.map(|predata| {
						let layout = predata.layout();
						let size = self.builder.ins().iconst(I64, layout.size as i64);
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
					// let mut layouts = Vec::new();
					// let mut offsets = Vec::new();
					// Get layout of the entire capture thing.
					// Allocate a pointer with that size.
					// (Could theoretically avoid allocation for small-enough captures?)
					// One by one, store each value to different offsets.
					// Assign pointer to symbol.
					todo!();
				}
				linear::Statement::Free(pointer) => {
					let pointer = self.emit_load(pointer).unwrap();
					let pointer = self.value(pointer);
					self.builder.ins().call(self.func_ref_free, &[pointer]);
				}
				linear::Statement::Call { symbol, procedure, captures, argument } => todo!(),
				// TODO: Optimize to call directly when possible.
				// self.function_builder.ins().call_indirect(SIG, callee, args)
			}
		}

		match preblock.terminator.as_ref().unwrap() {
			linear::Terminator::Abort => {
				self.builder.ins().trap(TrapCode::UnreachableCodeReached);
			}
			linear::Terminator::Return(argument) => {
				let argument = self.predata(argument);
				if let Some(argument) = argument {
					match self.result.unwrap() {
						ResultKind::Direct => {
							let value = self.value(argument);
							if let Some(pointer) = self.snapshot {
								let pointer = self.value(pointer);
								self.builder.ins().call(self.func_ref_free, &[pointer]);
							}
							self.builder.ins().return_(&[value]);
						}
						ResultKind::Indirect(dest) => {
							// NOTE: The result kind can only be indirect if the return value cannot be direct.
							let Data::Indirect(src, layout) = self.data(argument) else { panic!() };
							self.copy_memory(dest, src, layout);
							if let Some(pointer) = self.snapshot {
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
			linear::Terminator::Jump(_block, _arguments) => {
				// self.function_builder.ins().jump(block_call_label, block_call_args)
				todo!();
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
				self.builder.ins().br_table(data, jump_table);
			}
			linear::Terminator::CaseNat { index, limit, body, body_args, exit, exit_arg } => {
				todo!();
				// self.function_builder.ins().brif(c, block_then_label, block_then_args, block_else_label, block_else_args);
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
			linear::Register::Outer(n) => self.outer[n.0]?,
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
				linear::Projector::Captures => match predata {
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
						todo!()
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
	is_parameter_erased: bool,
	is_snapshot_erased: bool,
	is_result_erased: bool,
}

#[derive(Clone, Copy)]
struct DataLayout {
	size: u32,
	align: u8,
}

impl DataLayout {
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
	// TODO: This shouldn't concern whether it's empty, but whether its layout is empty.
	let snapshot_ty = (!prototype.outer.is_empty()).then_some(POINTER_TYPE);
	let result_ty = prototype.result.as_ref().map(|x| DataLayout::from(x).ty());

	let mut signature = Signature::new(CALL_CONV);
	if let Some(ty) = parameter_ty {
		signature.params.push(AbiParam::new(ty.unwrap_or(OVERSIZED_TYPE)));
	}
	if let Some(ty) = snapshot_ty {
		signature.params.push(AbiParam::new(ty));
	}
	if let Some(ty) = result_ty {
		signature.returns.push(AbiParam::new(ty.unwrap_or(OVERSIZED_TYPE)));
	}

	(
		signature,
		SignatureFlags {
			is_parameter_erased: parameter_ty.is_none(),
			is_snapshot_erased: snapshot_ty.is_none(),
			is_result_erased: result_ty.is_none(),
		},
	)
}
