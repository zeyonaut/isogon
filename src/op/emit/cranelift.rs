use std::collections::HashMap;

use cranelift::{
	codegen::{
		ir::{
			types::{I64, I8},
			AbiParam, Block, Function, InstBuilder, Signature, StackSlot, StackSlotData, StackSlotKind,
			TrapCode, Type, UserExternalName, UserFuncName, Value,
		},
		isa::CallConv,
	},
	frontend::{FunctionBuilder, FunctionBuilderContext},
};

use crate::{common::Symbol, ir::linear};

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
	let mut block_builder = BlockBuilder::new(&mut function_builder, signature_flags, entry);
	for (block, preblock) in blocks.iter().copied().zip(&procedure.blocks) {
		block_builder.process_parameters(block, preblock);
	}
	for (block, preblock) in blocks.iter().copied().zip(&procedure.blocks) {
		block_builder.build(block, preblock);
	}
	function_builder.seal_all_blocks();
	function_builder.finalize();
	function
}

struct BlockBuilder<'a, 'b> {
	function_builder: &'a mut FunctionBuilder<'b>,
	parameter: Option<Value>,
	snapshot: Option<Value>,
	locals: HashMap<Symbol, Option<EmittedRegister>>,
}

impl<'a, 'b> BlockBuilder<'a, 'b> {
	fn new(function_builder: &'a mut FunctionBuilder<'b>, flags: SignatureFlags, entry: Block) -> Self {
		let parameters = function_builder.block_params(entry);
		Self {
			parameter: (!flags.is_parameter_erased).then(|| parameters[0]),
			snapshot: (!flags.is_snapshot_erased).then(|| parameters[!flags.is_parameter_erased as usize]),
			locals: HashMap::new(),
			function_builder,
		}
	}

	fn process_parameters(&mut self, block: Block, preblock: &linear::Block) {
		self.function_builder.switch_to_block(block);

		for (symbol, layout) in preblock.parameters.iter() {
			let emitted_register = if let Some(layout) = layout {
				let concrete_layout = ConcreteLayout::from(layout);
				if let Some(ty) = type_of_layout(&concrete_layout) {
					self.function_builder.append_block_param(block, ty);
					Some(EmittedRegister::Small(*self.function_builder.block_params(block).last().unwrap()))
				} else {
					let slot = self.function_builder.create_sized_stack_slot(StackSlotData::new(
						StackSlotKind::ExplicitSlot,
						concrete_layout.size,
					));
					Some(EmittedRegister::Large(slot))
				}
			} else {
				None
			};
			self.locals.insert(*symbol, emitted_register);
		}
	}

	fn build(&mut self, block: Block, preblock: &linear::Block) {
		self.function_builder.switch_to_block(block);

		for statement in &preblock.statements {
			match statement {
				linear::Statement::Assign(_symbol, operation) => match operation {
					linear::Operation::Id(_) => todo!(),
					linear::Operation::Alloc(_) => todo!(),
					linear::Operation::Captures(_) => todo!(),
					linear::Operation::Suc(_) => todo!(),
				},
				linear::Statement::Free(_) => todo!(),
			}
		}

		match preblock.terminator.as_ref().unwrap() {
			linear::Terminator::Abort => {
				self.function_builder.ins().trap(TrapCode::UnreachableCodeReached);
			}
			linear::Terminator::Return(_argument) => {
				// self.function_builder.ins().return_(rvals);
			}
			linear::Terminator::Jump(_block, _arguments) => {
				// self.function_builder.ins().jump(block_call_label, block_call_args)
			}
			linear::Terminator::Split(_scrutinee, blocks) => {
				// TODO: Optimize to brif directly when possible.
				assert!(blocks.len() > 1);
				// What should we use for the default? The zero branch?
				// let _jump_table = self.function_builder.create_jump_table(JumpTableData::new(def, table));
				// self.function_builder.ins().br_table(x, JT);
			}
			linear::Terminator::CaseNat { index, limit, body, body_args, exit, exit_arg } => {
				// self.function_builder.ins().brif(c, block_then_label, block_then_args, block_else_label, block_else_args);
			}
			linear::Terminator::Apply { procedure, captures, argument, later } => {
				// TODO: Optimize to call directly when possible.
				// self.function_builder.ins().call_indirect(SIG, callee, args)
			}
		}
	}

	fn get(&mut self, register: linear::Register) -> Option<Value> {
		match register {
			linear::Register::Outer(_n) => todo!(),
			//	Some(self.function_builder.ins().iadd_imm(self.snapshot.unwrap(), todo!())),
			linear::Register::Parameter => self.parameter,
			linear::Register::Local(symbol) => Some(match self.locals[&symbol]? {
				EmittedRegister::Small(value) => value,
				EmittedRegister::Large(slot) => self.function_builder.ins().stack_addr(POINTER_TYPE, slot, 0),
			}),
		}
	}
}

struct SignatureFlags {
	is_parameter_erased: bool,
	is_snapshot_erased: bool,
	is_result_erased: bool,
}

struct ConcreteLayout {
	size: u32,
	alignment: u32,
}

impl From<&linear::Layout> for ConcreteLayout {
	fn from(value: &linear::Layout) -> Self {
		match value {
			linear::Layout::Byte => Self { size: 1, alignment: 1 },
			linear::Layout::Nat => Self { size: 8, alignment: 8 },
			linear::Layout::Ptr => Self { size: 8, alignment: 8 },
			linear::Layout::Fun => Self { size: 8 * 2, alignment: 8 },
			linear::Layout::Pair(pair) => {
				let layout_0 = Self::from(&pair[0]);
				let layout_1 = Self::from(&pair[1]);
				Self {
					size: layout_0.size.next_multiple_of(layout_1.alignment) + layout_1.size,
					alignment: layout_0.alignment.max(layout_1.alignment),
				}
			}
			linear::Layout::Array(n, layout) => {
				let layout = Self::from(layout.as_ref());
				Self {
					size: layout.size.next_multiple_of(layout.alignment) * n.0 as u32,
					alignment: layout.alignment,
				}
			}
		}
	}
}

fn type_of_layout(layout: &ConcreteLayout) -> Option<Type> {
	Some(match layout {
		ConcreteLayout { size: 1, alignment: 1 } => I8,
		ConcreteLayout { size: 8, alignment: 8 } => I64,
		_ => return None,
	})
}

fn emit_signature(prototype: &linear::Prototype) -> (Signature, SignatureFlags) {
	let parameter_ty = prototype.parameter.1.as_ref().map(ConcreteLayout::from).as_ref().map(type_of_layout);
	// TODO: This shouldn't concern whether it's empty, but whether its layout is empty.
	let snapshot_ty = (!prototype.outer.is_empty()).then_some(POINTER_TYPE);
	let result_ty = prototype.result.as_ref().map(ConcreteLayout::from).as_ref().map(type_of_layout);

	let mut signature = Signature::new(CallConv::SystemV);
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

enum Operand {
	ByValue(Value),
	ByRef(Value),
}

#[derive(Clone, Copy)]
enum EmittedRegister {
	Small(Value),
	Large(StackSlot),
}
