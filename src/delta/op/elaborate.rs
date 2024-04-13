use std::{
	ops::{Deref, DerefMut},
	rc::Rc,
};

use lasso::Resolver;

use super::{unelaborate::Unelaborate, unparse::print};
use crate::{
	delta::{
		common::{bind, Binder, Closure, Cost, Cpy, Field, Index, Level, Name},
		ir::{
			presyntax::{
				Constructor, Expression, Former, ParsedPreterm, ParsedProgram, Pattern, Preterm, Projector,
			},
			semantics::{
				DynamicNeutral, DynamicValue, Environment, KindValue, StaticNeutral, StaticValue, Value,
			},
			source::LexedSource,
			syntax::{DynamicTerm, KindTerm, StaticTerm},
		},
		op::{
			conversion::Conversion,
			evaluate::{Evaluate, EvaluateWith},
			parse::report_line_error,
			unevaluate::Unevaluate,
		},
	},
	utility::bx,
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(
	source: &str,
	lexed_source: &LexedSource,
	program: ParsedProgram,
	interner: &impl Resolver,
) -> (DynamicTerm, DynamicValue) {
	// TODO: Offer option to choose fragment, rather than force fragment to be 1.
	match synthesize_dynamic(
		&mut Context::empty(if program.fragment == 0 { Fragment::Logical } else { Fragment::Material }),
		program.expr,
	) {
		Ok((term, ty, ..)) => (term, ty),
		Err(error) => {
			report_line_error(
				source,
				lexed_source.ranges.get(error.range.0).copied().unwrap_or((source.len(), source.len() + 1)),
				&display_error(error.kind, interner),
			);
			panic!();
		}
	}
}

fn display_error(kind: ElaborationErrorKind, interner: &impl Resolver) -> String {
	match kind {
		ElaborationErrorKind::StaticBidirectionalMismatch { synthesized, expected } => {
			println!("elaboration error: type mismatch\nexpected: {synthesized:#?}\nfound: {expected:#?}");
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner).unwrap();
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner).unwrap();
			format!("elaboration error: type mismatch\nexpected: {}\nfound: {}", ty_ex, ty_sy)
		}
		ElaborationErrorKind::DynamicBidirectionalMismatch { synthesized, expected } => {
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner).unwrap();
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner).unwrap();
			format!("elaboration error: type mismatch\nexpected: {}\nfound: {}", ty_ex, ty_sy)
		}
		_ => format!("elaboration error: {:#?}", kind),
	}
}

#[derive(Debug, Clone)]
struct ElaborationError {
	range: (usize, usize),
	kind: ElaborationErrorKind,
}

#[derive(Debug, Clone)]
enum ExpectedFormer {
	Universe,
	Exp,
	Sigma,
	Pi,
	Lift,
	Bx,
	Wrap,
	Id,
}

#[derive(Debug, Clone)]
enum ElaborationErrorKind {
	LambdaGradeMismatch(usize, usize),
	ExpectedStaticFoundDynamicVariable,
	ExpectedDynamicFoundStaticVariable,
	UsedNonCrispLockedVariable,
	VariableHasUsesLeft(usize),
	SynthesizedLambdaOrPair,
	InvalidFormer,
	InvalidConstructor,
	InvalidProjector,
	ExpectedFormer(ExpectedFormer),
	SynthesizedFormer(ExpectedFormer),
	StaticBidirectionalMismatch { synthesized: StaticTerm, expected: StaticTerm },
	DynamicBidirectionalMismatch { synthesized: DynamicTerm, expected: DynamicTerm },
	InvalidCaseSplit,
	InvalidCaseSplitScrutineeType,
	CouldNotSynthesizeStatic,
	CouldNotSynthesizeDynamic,
	NotInScope,
	FiberAxesDependentOnBasepoint,
	RanOutOfVariableUses,
}

impl ElaborationErrorKind {
	fn at(self, range: (usize, usize)) -> ElaborationError { ElaborationError { range, kind: self } }
}

#[derive(Clone, Debug)]
pub enum ContextType {
	Static(StaticValue),
	// Type, kind.
	Dynamic(DynamicValue, KindValue),
}

#[derive(Clone, Debug)]
pub struct ContextEntry {
	is_crisp: bool,
	grade: Cost,
	ty: ContextType,
}

impl ContextEntry {
	pub fn new(is_crisp: bool, grade: Cost, ty: ContextType) -> Self { Self { is_crisp, grade, ty } }
}

pub struct LockedContext<'c> {
	context: &'c mut Context,
	old_lock: Option<usize>,
}

impl<'c> LockedContext<'c> {
	fn new(ctx: &'c mut Context, should_lock: bool) -> Self {
		Self { old_lock: should_lock.then(|| std::mem::replace(&mut ctx.lock, ctx.tys.len())), context: ctx }
	}
}

impl<'c> Deref for LockedContext<'c> {
	type Target = Context;

	fn deref(&self) -> &Self::Target { self.context }
}

impl<'c> DerefMut for LockedContext<'c> {
	fn deref_mut(&mut self) -> &mut Self::Target { self.context }
}

impl<'c> Drop for LockedContext<'c> {
	fn drop(&mut self) {
		if let Some(old_lock) = self.old_lock {
			self.context.lock = old_lock
		}
	}
}

pub struct AmplifiedContext<'c> {
	context: &'c mut Context,
}

impl<'c> AmplifiedContext<'c> {
	fn new(ctx: &'c mut Context, amplifier: Cost) -> Self {
		ctx.amplifiers.push((ctx.len().0, amplifier));
		Self { context: ctx }
	}
}

impl<'c> Deref for AmplifiedContext<'c> {
	type Target = Context;

	fn deref(&self) -> &Self::Target { self.context }
}

impl<'c> DerefMut for AmplifiedContext<'c> {
	fn deref_mut(&mut self) -> &mut Self::Target { self.context }
}

impl<'c> Drop for AmplifiedContext<'c> {
	fn drop(&mut self) { self.context.amplifiers.pop(); }
}

pub struct ExtendedContext<'c> {
	context: &'c mut Context,
}

impl<'c> ExtendedContext<'c> {
	fn new(ctx: &'c mut Context, name: Option<Name>, entry: ContextEntry, value: Value) -> Self {
		ctx.tys.push((name, entry));
		ctx.environment.push(value);
		Self { context: ctx }
	}

	fn free(self) -> Result<(), ElaborationErrorKind> {
		let grade = self.tys.last().unwrap().1.grade;
		if let Cost::Fin(grade) = grade {
			(grade == 0).then_some(()).ok_or(ElaborationErrorKind::VariableHasUsesLeft(grade))
		} else {
			Ok(())
		}
	}
}

impl<'c> Deref for ExtendedContext<'c> {
	type Target = Context;

	fn deref(&self) -> &Self::Target { self.context }
}

impl<'c> DerefMut for ExtendedContext<'c> {
	fn deref_mut(&mut self) -> &mut Self::Target { self.context }
}

impl<'c> Drop for ExtendedContext<'c> {
	fn drop(&mut self) {
		self.tys.pop();
		self.environment.pop();
	}
}

pub struct ErasedContext<'c> {
	context: &'c mut Context,
	old_fragment: Fragment,
}

impl<'c> ErasedContext<'c> {
	fn new(ctx: &'c mut Context, fragment: Fragment) -> Self {
		Self { old_fragment: std::mem::replace(&mut ctx.fragment, fragment), context: ctx }
	}
}

impl<'c> Deref for ErasedContext<'c> {
	type Target = Context;

	fn deref(&self) -> &Self::Target { self.context }
}

impl<'c> DerefMut for ErasedContext<'c> {
	fn deref_mut(&mut self) -> &mut Self::Target { self.context }
}

impl<'c> Drop for ErasedContext<'c> {
	fn drop(&mut self) { self.context.fragment = self.old_fragment }
}

#[derive(Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum Fragment {
	Logical = 0,
	Material = 1,
}

pub struct Context {
	fragment: Fragment,
	lock: usize,
	amplifiers: Vec<(usize, Cost)>,
	environment: Environment,
	tys: Vec<(Option<Name>, ContextEntry)>,
}

impl Context {
	pub fn empty(fragment: Fragment) -> Self {
		Self {
			fragment,
			lock: 0,
			amplifiers: Vec::new(),
			environment: Environment(Vec::new()),
			tys: Vec::new(),
		}
	}

	pub fn len(&self) -> Level { Level(self.environment.0.len()) }

	// Uses a resource.
	fn take_index(&mut self, index: usize) -> Result<(), ElaborationErrorKind> {
		let level = self.tys.len() - (index + 1);

		if !self.tys[level].1.is_crisp && level < self.lock {
			return Err(ElaborationErrorKind::UsedNonCrispLockedVariable);
		}

		// Skip this for fragment 0, as 0 is absorbing under multiplication.
		let usage = if self.fragment == Fragment::Logical {
			Cost::Fin(0)
		} else {
			self
				.amplifiers
				.iter()
				.rev()
				.take_while(|(len, _)| level < *len)
				.fold(Cost::Fin(1), |agg, (_, amp)| agg * *amp)
		};

		if let Cost::Fin(grade) = &mut self.tys[level].1.grade {
			if let Cost::Fin(usage) = usage {
				*grade = grade.checked_sub(usage).ok_or(ElaborationErrorKind::RanOutOfVariableUses)?;
			} else {
				return Err(ElaborationErrorKind::RanOutOfVariableUses);
			}
		}

		Ok(())
	}

	pub fn erase(&mut self) -> ErasedContext<'_> { self.erase_if(true) }

	pub fn erase_if(&mut self, should_erase: bool) -> ErasedContext<'_> {
		ErasedContext::new(self, if should_erase { Fragment::Logical } else { self.fragment })
	}

	pub fn lock_if(&mut self, should_lock: bool) -> LockedContext<'_> { LockedContext::new(self, should_lock) }

	pub fn amplify(&mut self, amplifier: impl Into<Cost>) -> AmplifiedContext<'_> {
		AmplifiedContext::new(self, amplifier.into())
	}

	pub fn bind_static(
		&mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Cost,
		copy: Cpy,
		ty: StaticValue,
	) -> ExtendedContext<'_> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(
				is_crisp,
				if copy == Cpy::Nt || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Static(ty),
			),
			Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))),
		)
	}

	pub fn bind_dynamic(
		&mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Cost,
		ty: DynamicValue,
		kind: KindValue,
	) -> ExtendedContext<'_> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(
				is_crisp,
				if !kind.copy.is_trivial() || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Dynamic(ty, kind),
			),
			Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))),
		)
	}

	pub fn extend_static(
		&mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Cost,
		copy: Cpy,
		ty: StaticValue,
		value: StaticValue,
	) -> ExtendedContext<'_> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(
				is_crisp,
				if copy == Cpy::Nt || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Static(ty),
			),
			Value::Static(value),
		)
	}

	pub fn extend_dynamic(
		&mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Cost,
		ty: DynamicValue,
		kind: KindValue,
		value: DynamicValue,
	) -> ExtendedContext<'_> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(
				is_crisp,
				if !kind.copy.is_trivial() || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Dynamic(ty, kind),
			),
			Value::Dynamic(value),
		)
	}
}

fn synthesize_static(
	ctx: &mut Context,
	expr: Expression,
) -> Result<(StaticTerm, StaticValue), ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match preterm {
		// Variables.
		Preterm::Variable(name) => 'var: {
			for (i, (name_1, entry)) in ctx.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Static(ty) = &entry.ty {
						let result = (StaticTerm::Variable(Some(name), Index(i)), ty.clone());
						ctx.take_index(i).map_err(|e| e.at(expr.range))?;
						break 'var result;
					} else {
						return Err(ElaborationErrorKind::ExpectedStaticFoundDynamicVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		}

		// Let-expressions.
		Preterm::Let { is_meta: true, grade, ty, argument, tail } => elaborate_static_let(
			ctx,
			expr.range,
			PreLet { grade, ty: *ty, argument: *argument, tail },
			(),
			|ctx, tail_body, ()| synthesize_static(ctx, tail_body),
			|grade, ty, argument, parameters, (tail, tail_ty)| {
				(
					StaticTerm::Let { grade, ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) },
					tail_ty,
				)
			},
		)?,

		// Quoting.
		Preterm::SwitchLevel(quotee) => {
			let (quotee, quotee_ty, kind) = synthesize_dynamic(ctx, *quotee)?;
			(StaticTerm::Quote(bx!(quotee)), StaticValue::Lift { ty: quotee_ty, kind: kind.into() })
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if ctx.fragment == Fragment::Logical => {
			let (base, base_copy) = elaborate_static_type(ctx, *base)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let [parameter] = family.parameters;
			let (family, family_copy) = {
				let mut context = ctx.bind_static(parameter, false, 0.into(), base_copy, base_value);
				let family = elaborate_static_type(&mut context, *family.body)?;
				context.free().map_err(|e| e.at(expr.range))?;
				family
			};
			(
				StaticTerm::Pi { grade, base_copy, base: base.into(), family: bind([parameter], family) },
				StaticValue::Universe(family_copy),
			)
		}
		Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::Call { callee, argument } => {
			let (callee, scrutinee_ty) = synthesize_static(ctx, *callee)?;
			let StaticValue::IndexedProduct { grade, base, family, .. } = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument =
				verify_static(&mut ctx.amplify(grade).erase_if(grade == 0), *argument, (*base).clone())?;
			(
				StaticTerm::Apply { scrutinee: bx!(callee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&ctx.environment)]),
			)
		}

		// Dependent pairs.
		Preterm::Sg { base, family } => {
			let (base, base_copy) = elaborate_static_type(ctx, *base)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let [parameter] = family.parameters;
			let (family, family_copy) = {
				let mut context = ctx.bind_static(parameter, false, 0.into(), base_copy, base_value);
				let family = elaborate_static_type(&mut context, *family.body)?;
				context.free().map_err(|e| e.at(expr.range))?;
				family
			};
			(
				StaticTerm::Sg { base_copy, base: base.into(), family_copy, family: bind([parameter], family) },
				StaticValue::Universe(base_copy.max(family_copy)),
			)
		}
		Preterm::Pair { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::SgLet { grade, argument, tail } => elaborate_static_sg_let(
			ctx,
			expr.range,
			PreSgLet { grade, argument: *argument, tail },
			(),
			|ctx, tail_body, ()| synthesize_static(ctx, tail_body),
			|grade, argument, parameters, (tail, tail_ty)| {
				(StaticTerm::SgLet { grade, argument: argument.into(), tail: bind(parameters, tail) }, tail_ty)
			},
		)?,

		// Generic type formers.
		Preterm::Former(former, arguments) if ctx.fragment == Fragment::Logical => match former {
			// Types and universe indices.
			Former::Universe => {
				let [c] = arguments.try_into().unwrap();
				let ParsedPreterm(Preterm::Constructor(Constructor::Cpy(c), v)) = c.preterm else { panic!() };
				assert!(v.is_empty());
				(StaticTerm::Universe(c), StaticValue::Universe(Cpy::Tr))
			}
			Former::Copy if arguments.is_empty() => (StaticTerm::Cpy, StaticValue::Universe(Cpy::Tr)),
			Former::Repr if arguments.is_empty() => (StaticTerm::Repr, StaticValue::Universe(Cpy::Tr)),

			// Quoting.
			Former::Lift => {
				let [liftee] = arguments.try_into().unwrap();
				let (liftee, kind) = elaborate_dynamic_type(ctx, liftee)?;
				(
					StaticTerm::Lift { liftee: liftee.into(), kind: kind.unevaluate_in(ctx.len()).into() },
					StaticValue::Universe(Cpy::Nt),
				)
			}

			// Repeated programs.
			Former::Exp(grade) => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, c) = elaborate_static_type(ctx, ty)?;
				(StaticTerm::Exp(grade, ty.into()), StaticValue::Universe(c))
			}

			// Enumerated numbers.
			Former::Enum(card) if arguments.is_empty() =>
				(StaticTerm::Enum(card), StaticValue::Universe(Cpy::Tr)),

			// Natural numbers.
			Former::Nat if arguments.is_empty() => (StaticTerm::Nat, StaticValue::Universe(Cpy::Tr)),

			// Invalid former.
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},

		// Generic term constructors.
		Preterm::Constructor(constructor, arguments) => match constructor {
			// Universe indices.
			Constructor::Cpy(c) if ctx.fragment == Fragment::Logical && arguments.is_empty() => (
				match c {
					Cpy::Tr => StaticTerm::CpyMax(vec![]),
					Cpy::Nt => StaticTerm::CpyNt,
				},
				StaticValue::Cpy,
			),
			Constructor::CpyMax if ctx.fragment == Fragment::Logical => (
				StaticTerm::CpyMax(
					arguments
						.into_iter()
						.map(|a| verify_static(&mut ctx.erase(), a, StaticValue::Cpy))
						.collect::<Result<_, _>>()?,
				),
				StaticValue::Cpy,
			),
			Constructor::ReprAtom(r) if ctx.fragment == Fragment::Logical && arguments.is_empty() =>
				(StaticTerm::ReprAtom(r), StaticValue::ReprType),
			Constructor::ReprPair if ctx.fragment == Fragment::Logical => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(&mut ctx.erase(), r0, StaticValue::ReprType)?;
				let r1 = verify_static(&mut ctx.erase(), r1, StaticValue::ReprType)?;
				(StaticTerm::ReprPair(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}

			// Repeated programs.
			Constructor::Exp(grade) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty) = synthesize_static(&mut ctx.erase(), tm)?;
				(StaticTerm::Repeat(grade, tm.into()), StaticValue::Exp(grade, ty.into()))
			}

			// Enumerated numbers.
			Constructor::Enum(k, v) if arguments.is_empty() =>
				(StaticTerm::EnumValue(k, v), StaticValue::Enum(k)),

			// Natural numbers.
			Constructor::Num(n) if arguments.is_empty() => (StaticTerm::Num(n), StaticValue::Nat),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_static(ctx, prev, StaticValue::Nat)?;
				if let StaticTerm::Num(p) = prev {
					(StaticTerm::Num(p + 1), StaticValue::Nat)
				} else {
					(StaticTerm::Suc(prev.into()), StaticValue::Nat)
				}
			}

			// Invalid constructor.
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},

		// Generic projectors.
		Preterm::Project(scrutinee, projector) => match projector {
			// Dependent pairs.
			Projector::Field(field) if ctx.fragment == Fragment::Logical => {
				let (scrutinee, scrutinee_ty) = synthesize_static(&mut ctx.erase(), *scrutinee)?;
				let StaticValue::IndexedSum { base, family, .. } = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				match field {
					Field::Base => (StaticTerm::SgField(scrutinee.into(), field), base.as_ref().clone()),
					Field::Fiber => (
						StaticTerm::SgField(bx!(scrutinee.clone()), field),
						family
							.evaluate_with([StaticTerm::SgField(scrutinee.clone().into(), Field::Base)
								.evaluate_in(&ctx.environment)]),
					),
				}
			}

			// Invalid projector.
			_ => return Err(ElaborationErrorKind::InvalidProjector.at(expr.range)),
		},

		// Generic case splits.
		Preterm::Split { scrutinee, is_cast: false, motive, cases } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(ctx, *scrutinee)?;
			let scrutinee_value = scrutinee.clone().evaluate_in(&ctx.environment);
			match scrutinee_ty {
				StaticValue::Enum(card) => {
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == card as _)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					let (motive_term, _) = elaborate_static_type(
						&mut ctx.bind_static(motive_parameter, false, 0.into(), Cpy::Tr, StaticValue::Enum(card)),
						*motive.body,
					)?;
					let motive_value =
						Closure::new(ctx.environment.clone(), [motive_parameter], motive_term.clone());
					// TODO: Avoid cloning.
					let mut new_cases = Vec::new();
					for v in 0..card {
						let v = v as u8;
						let case = cases[cases
							.iter()
							.position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::Enum(target_card, target_v), args) = pattern
								{
									*target_card == card && *target_v == v && args.is_empty()
								} else {
									false
								}
							})
							.unwrap()]
						.1
						.clone();
						new_cases.push(verify_static(
							ctx,
							case,
							motive_value.evaluate_with([StaticValue::EnumValue(card, v)]),
						)?)
					}

					(
						StaticTerm::CaseEnum {
							scrutinee: bx!(scrutinee),
							motive: bind([motive_parameter], motive_term),
							cases: new_cases,
						},
						motive_value.evaluate_with([scrutinee_value]),
					)
				}

				// Natural numbers.
				StaticValue::Nat => {
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == 2)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					let (motive, motive_c) = elaborate_static_type(
						&mut ctx.bind_static(motive_parameter, false, 0.into(), Cpy::Tr, StaticValue::Nat),
						*motive.body,
					)?;
					let motive_value = Closure::new(ctx.environment.clone(), [motive_parameter], motive.clone());
					// Avoid cloning.
					let case_nil_position = cases
						.iter()
						.position(|(pattern, _)| {
							if let Pattern::Construction(Constructor::Num(0), args) = pattern {
								args.is_empty()
							} else {
								false
							}
						})
						.unwrap();
					let case_nil = cases[case_nil_position].1.clone();
					let (index, witness) = {
						let Pattern::Construction(Constructor::Suc, args) = cases[1 - case_nil_position].0.clone()
						else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let [arg] = args.try_into().unwrap();
						let Pattern::Witness { index, witness } = arg else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						(index, witness)
					};
					let case_suc = cases[1 - case_nil_position].1.clone();
					let case_nil =
						verify_static(ctx, case_nil, motive_value.evaluate_with([StaticValue::Num(0)]))?;
					let case_suc = {
						// Effectively disallow using nontrivial resources in recursive case.
						let mut ctx = ctx.amplify(Cost::Inf);
						let mut ctx = ctx.bind_static(index, false, Cost::Inf, Cpy::Tr, StaticValue::Nat);
						let index_level = ctx.len().index(0);
						let fragment = ctx.fragment;
						let result = {
							let mut ctx = ctx.bind_static(
								witness,
								false,
								(fragment as usize).into(),
								motive_c,
								motive_value.evaluate_with([(index, index_level).into()]),
							);
							let result = verify_static(
								&mut ctx,
								case_suc,
								motive_value.evaluate_with([StaticValue::Neutral(StaticNeutral::Suc(Rc::new(
									(index, index_level).into(),
								)))]),
							)?;
							ctx.free().map_err(|e| e.at(expr.range))?;
							result
						};
						ctx.free().map_err(|e| e.at(expr.range))?;
						result
					};
					(
						StaticTerm::CaseNat {
							scrutinee: bx!(scrutinee),
							motive: bind([motive_parameter], motive),
							case_nil: bx!(case_nil),
							case_suc: bind([index, witness], case_suc),
						},
						motive_value.evaluate_with([scrutinee_value]),
					)
				}

				// Invalid case split.
				_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
			}
		}
		// Synthesis failure.
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeStatic.at(expr.range)),
	})
}

fn verify_static(
	ctx: &mut Context,
	expr: Expression,
	ty: StaticValue,
) -> Result<StaticTerm, ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match (preterm, ty) {
		// Let-expressions.
		(Preterm::Let { is_meta: true, grade, ty, argument, tail }, tail_ty) => elaborate_static_let(
			ctx,
			expr.range,
			PreLet { grade, ty: *ty, argument: *argument, tail },
			tail_ty,
			verify_static,
			|grade, ty, argument, parameters, tail| StaticTerm::Let {
				grade,
				ty: bx!(ty),
				argument: bx!(argument),
				tail: bind(parameters, tail),
			},
		)?,

		// Quoted programs.
		(Preterm::SwitchLevel(quotee), ty) => {
			let StaticValue::Lift { ty: liftee, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			let quotee = verify_dynamic(ctx, *quotee, liftee)?;
			StaticTerm::Quote(bx!(quotee))
		}

		// Dependent functions.
		(
			Preterm::Lambda { grade, body },
			StaticValue::IndexedProduct { grade: grade_v, base_copy, base, family },
		) => {
			(grade * ctx.fragment as usize == grade_v * ctx.fragment as usize)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_v).at(expr.range))?;
			let parameters = body.parameters;
			let mut context = ctx.bind_static(
				parameters[0],
				false,
				(grade * ctx.fragment as usize).into(),
				base_copy,
				base.as_ref().clone(),
			);
			let basepoint_level = context.len().index(0);
			let body = verify_static(
				&mut context,
				*body.body,
				family.evaluate_with([(parameters[0], basepoint_level).into()]),
			)?;
			context.free().map_err(|e| e.at(expr.range))?;
			StaticTerm::Function(grade, bind(parameters, body))
		}

		// Dependent pairs.
		(
			Preterm::Pair { basepoint, fiberpoint },
			StaticValue::IndexedSum { base_copy: _, base, family_copy: _, family },
		) => {
			let basepoint = verify_static(ctx, *basepoint, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&ctx.environment);
			let fiberpoint = verify_static(ctx, *fiberpoint, family.evaluate_with([basepoint_value]))?;
			StaticTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
		}
		(Preterm::SgLet { grade, argument, tail }, tail_ty) => elaborate_static_sg_let(
			ctx,
			expr.range,
			PreSgLet { grade, argument: *argument, tail },
			tail_ty,
			verify_static,
			|grade, argument, parameters, tail| StaticTerm::SgLet {
				grade,
				argument: argument.into(),
				tail: bind(parameters, tail),
			},
		)?,

		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(ctx, term.at(expr.range))?;
			if ctx.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				return Err(
					ElaborationErrorKind::StaticBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(ctx.len()),
						expected: ty.unevaluate_in(ctx.len()),
					}
					.at(expr.range),
				);
			}
		}
	})
}

// TODO: Refactor to centralize assigning copy/repr to each type to prevent potential mistakes.
// Term, type, copyability, representation
fn synthesize_dynamic(
	ctx: &mut Context,
	expr: Expression,
) -> Result<(DynamicTerm, DynamicValue, KindValue), ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match preterm {
		// Variables.
		Preterm::Variable(name) => 'var: {
			for (i, (name_1, entry)) in ctx.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Dynamic(ty, kind) = &entry.ty {
						let result = (DynamicTerm::Variable(Some(name), Index(i)), ty.clone(), kind.clone());
						ctx.take_index(i).map_err(|e| e.at(expr.range))?;
						break 'var result;
					} else {
						return Err(ElaborationErrorKind::ExpectedDynamicFoundStaticVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		}

		// Let-expressions.
		Preterm::Let { is_meta, grade, ty, argument, tail } =>
			if is_meta {
				elaborate_static_let(
					ctx,
					expr.range,
					PreLet { grade, ty: *ty, argument: *argument, tail },
					(),
					|ctx, tail_body, ()| synthesize_dynamic(ctx, tail_body),
					|grade, ty, argument, parameters, (tail, tail_ty, tail_kind)| {
						(
							DynamicTerm::Def {
								grade,
								ty: ty.into(),
								argument: argument.into(),
								tail: bind(parameters, tail),
							},
							tail_ty,
							tail_kind,
						)
					},
				)?
			} else {
				elaborate_dynamic_let(
					ctx,
					expr.range,
					PreLet { grade, ty: *ty, argument: *argument, tail },
					(),
					|ctx, tail_body, ()| synthesize_dynamic(ctx, tail_body),
					|grade, ty, argument_kind, argument, parameters, (tail, tail_ty, tail_kind)| {
						(
							DynamicTerm::Let {
								grade,
								ty: ty.into(),
								argument_kind: argument_kind.into(),
								argument: argument.into(),
								tail: bind(parameters, tail),
							},
							tail_ty,
							tail_kind,
						)
					},
				)?
			},

		// Splicing.
		Preterm::SwitchLevel(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, kind }) = synthesize_static(ctx, *splicee)? else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*kind).clone())
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if ctx.fragment == Fragment::Logical => {
			let (base, base_kind) = elaborate_dynamic_type(ctx, *base)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let parameters = family.parameters;
			let (family, family_kind) = {
				let mut context = ctx.bind_dynamic(parameters[0], false, 0.into(), base_value, base_kind.clone());
				let result = elaborate_dynamic_type(&mut context, *family.body)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let Ok(family_kind) = family_kind.try_unevaluate_in(ctx.len()) else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Pi {
					grade,
					base_kind: base_kind.unevaluate_in(ctx.len()).into(),
					base: base.into(),
					family_kind: family_kind.into(),
					family: bind(parameters, family),
				},
				DynamicValue::Universe { kind: KindValue::fun().into() },
				KindValue::ty(),
			)
		}
		Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::Call { callee, argument } => {
			let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(ctx, *callee)?;
			let DynamicValue::IndexedProduct { grade, base, family_kind, family, .. } = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument =
				verify_dynamic(&mut ctx.amplify(grade).erase_if(grade == 0), *argument, (*base).clone())?;
			let argument_value = argument.clone().evaluate_in(&ctx.environment);
			(
				DynamicTerm::Apply {
					scrutinee: scrutinee.into(),
					grade: Some(grade),
					argument: argument.into(),
					family_kind: Some(family_kind.unevaluate_in(ctx.len()).into()),
				},
				family.evaluate_with([argument_value]),
				(*family_kind).clone(),
			)
		}

		// Dependent pairs.
		Preterm::Sg { base, family } if ctx.fragment == Fragment::Logical => {
			let (base, base_kind) = elaborate_dynamic_type(ctx, *base)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let parameters = family.parameters;
			let (family, family_kind) = {
				let mut ctx = ctx.bind_dynamic(parameters[0], false, 0.into(), base_value, base_kind.clone());
				let result = elaborate_dynamic_type(&mut ctx, *family.body)?;
				ctx.free().map_err(|e| e.at(expr.range))?;
				result
			};

			let kind = KindValue::pair(ctx.len(), base_kind.clone(), family_kind.clone());

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let Ok(family_kind) = family_kind.try_unevaluate_in(ctx.len()) else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Sg {
					base_kind: base_kind.unevaluate_in(ctx.len()).into(),
					base: base.into(),
					family_kind: family_kind.into(),
					family: bind(parameters, family),
				},
				DynamicValue::Universe { kind: kind.into() },
				KindValue::ty(),
			)
		}
		Preterm::Pair { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::SgLet { grade, argument, tail } => elaborate_dynamic_sg_let(
			ctx,
			expr.range,
			PreSgLet { grade, argument: *argument, tail },
			(),
			|ctx, tail_body, ()| synthesize_dynamic(ctx, tail_body),
			|grade, kinds, argument, parameters, (tail, tail_ty, kind)| {
				(
					DynamicTerm::SgLet { grade, kinds, argument: argument.into(), tail: bind(parameters, tail) },
					tail_ty,
					kind,
				)
			},
		)?,

		// Generic type formers.
		Preterm::Former(former, arguments) if ctx.fragment == Fragment::Logical => match former {
			// Types.
			Former::Universe => {
				let [copy, repr] = arguments.try_into().unwrap();
				let copy = verify_static(&mut ctx.erase(), copy, StaticValue::Cpy)?;
				let repr = verify_static(&mut ctx.erase(), repr, StaticValue::ReprType)?;
				(
					DynamicTerm::Universe { kind: KindTerm { copy, repr }.into() },
					DynamicValue::Universe { kind: KindValue::ty().into() },
					KindValue::ty(),
				)
			}

			// Repeated programs.
			Former::Exp(Cost::Fin(grade)) => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, kind) = elaborate_dynamic_type(ctx, ty)?;
				(
					DynamicTerm::Exp(grade, kind.unevaluate_in(ctx.len()).into(), ty.into()),
					DynamicValue::Universe { kind: kind.exp(grade).into() },
					KindValue::ty(),
				)
			}

			// Enumerated numbers.
			Former::Enum(card) if arguments.is_empty() => (
				DynamicTerm::Enum(card),
				DynamicValue::Universe { kind: KindValue::enu().into() },
				KindValue::ty(),
			),

			// Paths.
			Former::Id => {
				let [ty, x, y] = arguments.try_into().unwrap();
				let (ty, kind) = elaborate_dynamic_type(ctx, ty)?;
				let ty_value = ty.clone().evaluate_in(&ctx.environment);
				let x = verify_dynamic(&mut ctx.erase(), x, ty_value.clone())?;
				let y = verify_dynamic(&mut ctx.erase(), y, ty_value.clone())?;
				(
					DynamicTerm::Id {
						kind: kind.unevaluate_in(ctx.len()).into(),
						space: ty.into(),
						left: x.into(),
						right: y.into(),
					},
					DynamicValue::Universe { kind: KindValue::path().into() },
					KindValue::ty(),
				)
			}

			// Natural numbers.
			Former::Nat if arguments.is_empty() =>
				(DynamicTerm::Nat, DynamicValue::Universe { kind: KindValue::nat().into() }, KindValue::ty()),

			// Wrappers.
			Former::Bx => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, kind) = elaborate_dynamic_type(ctx, ty)?;
				(
					DynamicTerm::Bx { kind: kind.unevaluate_in(ctx.len()).into(), inner: ty.into() },
					DynamicValue::Universe { kind: KindValue::ptr().into() },
					KindValue::ty(),
				)
			}
			Former::Wrap => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, kind) = elaborate_dynamic_type(ctx, ty)?;
				(
					DynamicTerm::Wrap { inner: ty.into(), kind: kind.unevaluate_in(ctx.len()).into() },
					DynamicValue::Universe { kind: kind.wrap().into() },
					KindValue::ty(),
				)
			}

			// Invalid former.
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},

		// Generic term constructors.
		Preterm::Constructor(constructor, arguments) => match constructor {
			// Repeated programs.
			Constructor::Exp(Cost::Fin(grade)) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm)?;
				(
					DynamicTerm::Repeat(grade, tm.into()),
					DynamicValue::Exp(grade, kind.clone().into(), ty.into()),
					kind.exp(grade),
				)
			}

			// Enumerated numbers.
			Constructor::Enum(k, v) if arguments.is_empty() =>
				(DynamicTerm::EnumValue(k, v), DynamicValue::Enum(k), KindValue::enu()),

			// Natural numbers.
			Constructor::Num(n) if arguments.is_empty() =>
				(DynamicTerm::Num(n), DynamicValue::Nat, KindValue::nat()),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_dynamic(ctx, prev, DynamicValue::Nat)?;
				if let DynamicTerm::Num(p) = prev {
					(DynamicTerm::Num(p + 1), DynamicValue::Nat, KindValue::nat())
				} else {
					(DynamicTerm::Suc(prev.into()), DynamicValue::Nat, KindValue::nat())
				}
			}

			// Wrappers.
			Constructor::Bx => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm)?;
				(
					DynamicTerm::BxValue(bx!(tm)),
					DynamicValue::Bx { inner: ty.into(), kind: kind.into() },
					KindValue::ptr(),
				)
			}
			Constructor::Wrap => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm)?;
				(
					DynamicTerm::WrapValue(bx!(tm)),
					DynamicValue::Wrap { inner: ty.into(), kind: kind.clone().into() },
					kind.wrap(),
				)
			}

			// Invalid constructor.
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},

		// Generic projectors.
		Preterm::Project(scrutinee, projector) => match projector {
			// Repeated programs.
			Projector::Exp if ctx.fragment == Fragment::Logical => {
				let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(&mut ctx.erase(), *scrutinee)?;
				let DynamicValue::Exp(n, kind, ty) = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(expr.range));
				};
				(DynamicTerm::ExpProject(scrutinee.into()), ty.as_ref().clone(), (*kind).clone())
			}

			// Dependent pairs.
			Projector::Field(field) if ctx.fragment == Fragment::Logical => {
				let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(&mut ctx.erase(), *scrutinee)?;
				let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				let basepoint = DynamicTerm::SgField { scrutinee: scrutinee.clone().into(), field: Field::Base };
				match field {
					Field::Base => (basepoint, base.as_ref().clone(), (*base_kind).clone()),
					Field::Fiber => (
						DynamicTerm::SgField { scrutinee: scrutinee.into(), field },
						family.evaluate_with([basepoint.evaluate_in(&ctx.environment)]),
						(*family_kind).clone(),
					),
				}
			}

			// Wrappers.
			Projector::Bx => {
				let (tm, DynamicValue::Bx { inner: ty, kind }, _) = synthesize_dynamic(ctx, *scrutinee)? else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Bx).at(expr.range));
				};
				(
					DynamicTerm::BxProject {
						scrutinee: tm.into(),
						kind: Some(kind.unevaluate_in(ctx.len()).into()),
					},
					ty.as_ref().clone(),
					(*kind).clone(),
				)
			}

			Projector::Wrap => {
				let (tm, DynamicValue::Wrap { inner: ty, kind }, _) = synthesize_dynamic(ctx, *scrutinee)? else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Wrap).at(expr.range));
				};
				(
					DynamicTerm::WrapProject {
						scrutinee: bx!(tm),
						kind: Some(kind.unevaluate_in(ctx.len()).into()),
					},
					ty.as_ref().clone(),
					(*kind).clone(),
				)
			}

			// Invalid projector.
			_ => return Err(ElaborationErrorKind::InvalidProjector.at(expr.range)),
		},

		// Generic case splits.
		Preterm::Split { scrutinee, is_cast, motive, cases } => {
			if is_cast {
				let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(&mut ctx.erase(), *scrutinee)?;
				let scrutinee_value = scrutinee.clone().evaluate_in(&ctx.environment);
				match scrutinee_ty {
					DynamicValue::Id { kind, space, left, right } => {
						// TODO: Handle this error.
						let [v, p] = (*motive.parameters).try_into().unwrap();
						let Ok([(Pattern::Construction(Constructor::Refl, pattern), case_refl)]) =
							<[_; 1]>::try_from(cases)
						else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let Ok([]) = <[_; 0]>::try_from(pattern) else {
							panic!();
						};

						// TODO: Throw specific error if copy/repr depend on the motive.
						let (motive_term, motive_kind) = {
							let mut context =
								ctx.bind_dynamic(v, false, 0.into(), (*space).clone(), (*kind).clone());
							let index_level = context.len().index(0);
							let mut context = context.bind_dynamic(
								p,
								false,
								0.into(),
								DynamicValue::Id {
									kind,
									space: space.clone(),
									left: left.clone(),
									right: DynamicValue::Neutral(DynamicNeutral::Variable(v, index_level)).into(),
								},
								// TODO: Refactor into a better place.
								KindValue::path(),
							);
							elaborate_dynamic_type(&mut context, *motive.body)?
						};
						let motive = Closure::new(ctx.environment.clone(), [v, p], motive_term.clone());

						let case_refl = verify_dynamic(
							ctx,
							case_refl,
							motive.evaluate_with([(*left).clone(), DynamicValue::Refl]),
						)?;

						(
							DynamicTerm::CasePath {
								scrutinee: scrutinee.into(),
								motive: bind([v, p], motive_term),
								case_refl: case_refl.into(),
							},
							motive.evaluate_with([(*right).clone(), scrutinee_value]),
							motive_kind,
						)
					}

					// Invalid case split.
					_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
				}
			} else {
				let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(ctx, *scrutinee)?;
				let scrutinee_value = scrutinee.clone().evaluate_in(&ctx.environment);
				match scrutinee_ty {
					// Enumerated numbers.
					DynamicValue::Enum(card) => {
						// TODO: Handle this error.
						let [motive_parameter] = (*motive.parameters).try_into().unwrap();
						(cases.len() == card as _)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						// TODO: Throw specific error if copy/repr depend on the motive.
						let (motive_term, motive_kind) = elaborate_dynamic_type(
							&mut ctx.bind_dynamic(
								motive_parameter,
								false,
								0.into(),
								DynamicValue::Enum(card),
								KindValue::enu(),
							),
							*motive.body,
						)?;
						let motive = Closure::new(ctx.environment.clone(), [motive_parameter], motive_term.clone());
						// TODO: Avoid cloning.
						let mut new_cases = Vec::new();
						for v in 0..card {
							let v = v as u8;
							let case = cases[cases
								.iter()
								.position(|(pattern, _)| {
									if let Pattern::Construction(Constructor::Enum(target_card, target_v), args) =
										pattern
									{
										*target_card == card && *target_v == v && args.is_empty()
									} else {
										false
									}
								})
								.unwrap()]
							.1
							.clone();
							new_cases.push(verify_dynamic(
								ctx,
								case,
								motive.evaluate_with([DynamicValue::EnumValue(card, v)]),
							)?)
						}
						(
							DynamicTerm::CaseEnum {
								scrutinee: bx!(scrutinee),
								cases: new_cases,
								motive: bind([motive_parameter], motive_term),
								motive_kind: Some(motive_kind.unevaluate_in(ctx.len()).into()),
							},
							motive.evaluate_with([scrutinee_value]),
							motive_kind,
						)
					}

					// Paths. // TODO: Allow grade-0 matching on refl in fragment 1.
					DynamicValue::Id { kind, space, left, right } if ctx.fragment == Fragment::Logical => {
						// TODO: Something more like:
						// let motive = elaborate_dynamic_motive([space, space, id(space, var(1), var(0))]);

						// TODO: Handle this error.
						let [v, p] = (*motive.parameters).try_into().unwrap();
						let Ok([(Pattern::Construction(Constructor::Refl, pattern), case_refl)]) =
							<[_; 1]>::try_from(cases)
						else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let Ok([]) = <[_; 0]>::try_from(pattern) else {
							panic!();
						};

						// TODO: Throw specific error if copy/repr depend on the motive.
						let (motive_term, motive_kind) = {
							let mut context =
								ctx.bind_dynamic(v, false, 0.into(), (*space).clone(), (*kind).clone());
							let index_level = context.len().index(0);
							let mut context = context.bind_dynamic(
								p,
								false,
								0.into(),
								DynamicValue::Id {
									kind,
									space: space.clone(),
									left: left.clone(),
									right: DynamicValue::Neutral(DynamicNeutral::Variable(v, index_level)).into(),
								},
								// TODO: Refactor into a better place.
								KindValue::path(),
							);
							elaborate_dynamic_type(&mut context, *motive.body)?
						};
						let motive = Closure::new(ctx.environment.clone(), [v, p], motive_term.clone());

						let case_refl = verify_dynamic(
							ctx,
							case_refl,
							motive.evaluate_with([(*left).clone(), DynamicValue::Refl]),
						)?;

						(
							DynamicTerm::CasePath {
								scrutinee: scrutinee.into(),
								motive: bind([v, p], motive_term),
								case_refl: case_refl.into(),
							},
							motive.evaluate_with([(*right).clone(), scrutinee_value]),
							motive_kind,
						)
					}

					// Natural numbers.
					DynamicValue::Nat => {
						// TODO: Handle this error.
						let [motive_parameter] = (*motive.parameters).try_into().unwrap();
						(cases.len() == 2)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						// TODO: Throw specific error if copy/repr depend on the motive.
						let (motive_term, motive_kind) = elaborate_dynamic_type(
							&mut ctx.bind_dynamic(
								motive_parameter,
								false,
								0.into(),
								DynamicValue::Nat,
								KindValue::nat(),
							),
							*motive.body,
						)?;
						let motive = Closure::new(ctx.environment.clone(), [motive_parameter], motive_term.clone());
						// Avoid cloning.
						let case_nil_position = cases
							.iter()
							.position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::Num(0), args) = pattern {
									args.is_empty()
								} else {
									false
								}
							})
							.unwrap();
						let case_nil = cases[case_nil_position].1.clone();
						let (index, witness) = {
							let Pattern::Construction(Constructor::Suc, args) =
								cases[1 - case_nil_position].0.clone()
							else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							let [arg] = args.try_into().unwrap();
							let Pattern::Witness { index, witness } = arg else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							(index, witness)
						};
						let case_suc = cases[1 - case_nil_position].1.clone();
						let case_nil = verify_dynamic(ctx, case_nil, motive.evaluate_with([DynamicValue::Num(0)]))?;
						// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
						let case_suc = {
							// Effectively disallow using nontrivial resources in recursive case.
							let mut ctx = ctx.amplify(Cost::Inf);
							// NOTE: Unrestricted usage is only "safe" because we're approximating Nat with a finite type.
							// For nontrivial Nat, we may wish to enclose the index with a thunk.
							let mut ctx =
								ctx.bind_dynamic(index, false, Cost::Inf, DynamicValue::Nat, KindValue::nat());
							let index_level = ctx.len().index(0);
							let result = {
								let fragment = ctx.fragment;
								let mut ctx = ctx.bind_dynamic(
									witness,
									false,
									(fragment as usize).into(),
									motive.evaluate_with([(index, index_level).into()]),
									motive_kind.clone(),
								);
								let result = verify_dynamic(
									&mut ctx,
									case_suc,
									motive.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(Rc::new(
										DynamicNeutral::Variable(index, index_level),
									)))]),
								)?;
								ctx.free().map_err(|e| e.at(expr.range))?;
								result
							};
							ctx.free().map_err(|e| e.at(expr.range))?;
							result
						};
						(
							DynamicTerm::CaseNat {
								scrutinee: bx!(scrutinee),
								motive_kind: Some(motive_kind.unevaluate_in(ctx.len()).into()),
								motive: bind([motive_parameter], motive_term),
								case_nil: bx!(case_nil),
								case_suc: bind([index, witness], case_suc),
							},
							motive.evaluate_with([scrutinee_value]),
							motive_kind,
						)
					}

					// Invalid case split.
					_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
				}
			}
		}

		// Synthesis failure.
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeDynamic.at(expr.range)),
	})
}

fn verify_dynamic(
	ctx: &mut Context,
	expr: Expression,
	ty: DynamicValue,
) -> Result<DynamicTerm, ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match (preterm, ty) {
		// Let-expressions.
		(Preterm::Let { is_meta, grade, ty, argument, tail }, tail_ty) =>
			if is_meta {
				elaborate_static_let(
					ctx,
					expr.range,
					PreLet { grade, ty: *ty, argument: *argument, tail },
					tail_ty,
					verify_dynamic,
					|grade, ty, argument, parameters, tail| DynamicTerm::Def {
						grade,
						ty: ty.into(),
						argument: argument.into(),
						tail: bind(parameters, tail),
					},
				)?
			} else {
				elaborate_dynamic_let(
					ctx,
					expr.range,
					PreLet { grade, ty: *ty, argument: *argument, tail },
					tail_ty,
					verify_dynamic,
					|grade, ty, argument_kind, argument, parameters, tail| DynamicTerm::Let {
						grade,
						ty: ty.into(),
						argument_kind: argument_kind.into(),
						argument: argument.into(),
						tail: bind(parameters, tail),
					},
				)?
			},

		// Dependent functions.
		(
			Preterm::Lambda { grade, body },
			DynamicValue::IndexedProduct { grade: grade_t, base, base_kind, family, family_kind },
		) => {
			(grade * ctx.fragment as usize == grade_t * ctx.fragment as usize)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_t).at(expr.range))?;
			let parameters = body.parameters;
			let mut context = ctx.bind_dynamic(
				parameters[0],
				false,
				(grade * ctx.fragment as usize).into(),
				base.as_ref().clone(),
				(*base_kind).clone(),
			);
			let basepoint_level = context.len().index(0);
			let body = verify_dynamic(
				&mut context,
				*body.body,
				family.evaluate_with([(parameters[0], basepoint_level).into()]),
			)?;
			context.free().map_err(|e| e.at(expr.range))?;
			DynamicTerm::Function {
				grade,
				body: bind(parameters, body),
				domain_kind: Some(base_kind.unevaluate_in(ctx.len()).into()),
				codomain_kind: Some(family_kind.unevaluate_in(ctx.len()).into()),
			}
		}

		// Dependent pairs.
		(Preterm::Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(ctx, *basepoint, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&ctx.environment);
			let fiberpoint = verify_dynamic(ctx, *fiberpoint, family.evaluate_with([basepoint_value]))?;
			DynamicTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
		}
		(Preterm::SgLet { grade, argument, tail }, tail_ty) => elaborate_dynamic_sg_let(
			ctx,
			expr.range,
			PreSgLet { grade, argument: *argument, tail },
			tail_ty,
			verify_dynamic,
			|grade, kinds, argument, parameters, tail| DynamicTerm::SgLet {
				grade,
				kinds,
				argument: argument.into(),
				tail: bind(parameters, tail),
			},
		)?,

		// Paths.
		(Preterm::Constructor(Constructor::Refl, tms), ty) if ctx.fragment == Fragment::Logical => {
			let DynamicValue::Id { left, right, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Id).at(expr.range));
			};
			assert!(ctx.len().can_convert(&*left, &right));

			let [] = tms.try_into().unwrap();
			DynamicTerm::Refl
		}

		// Wrappers.
		(Preterm::Constructor(Constructor::Bx, tms), ty) => {
			let DynamicValue::Bx { inner: ty, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Bx).at(expr.range));
			};
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(ctx, tm, ty.as_ref().clone())?;
			DynamicTerm::BxValue(bx!(tm))
		}
		(Preterm::Constructor(Constructor::Wrap, tms), ty) => {
			let DynamicValue::Wrap { inner: ty, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Wrap).at(expr.range));
			};
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(ctx, tm, ty.as_ref().clone())?;
			DynamicTerm::WrapValue(bx!(tm))
		}

		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty, _) = synthesize_dynamic(ctx, term.at(expr.range))?;
			if ctx.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				return Err(
					ElaborationErrorKind::DynamicBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(ctx.len()),
						expected: ty.unevaluate_in(ctx.len()),
					}
					.at(expr.range),
				);
			}
		}
	})
}

fn elaborate_static_type(ctx: &mut Context, expr: Expression) -> Result<(StaticTerm, Cpy), ElaborationError> {
	let expr_range = expr.range;
	let (term, StaticValue::Universe(c)) = synthesize_static(&mut ctx.erase(), expr)? else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
	};
	Ok((term, c))
}

fn elaborate_dynamic_type(
	ctx: &mut Context,
	expr: Expression,
) -> Result<(DynamicTerm, KindValue), ElaborationError> {
	let expr_range = expr.range;
	let (term, DynamicValue::Universe { kind }, _) = synthesize_dynamic(&mut ctx.erase(), expr)? else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
	};
	Ok((term, (*kind).clone()))
}

struct PreLet {
	grade: Option<Cost>,
	ty: Expression,
	argument: Expression,
	tail: Binder<Box<Expression>>,
}

fn elaborate_static_let<A, B>(
	ctx: &mut Context,
	expr_range: (usize, usize),
	PreLet { grade, ty, argument, tail }: PreLet,
	tail_a: A,
	elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
	produce_let: impl FnOnce(Cost, StaticTerm, StaticTerm, [Option<Name>; 1], B) -> B,
) -> Result<B, ElaborationError> {
	let grade = grade.unwrap_or_else(|| if tail.parameter().is_some() { 1 } else { 0 }.into());
	let (ty, ty_c) = elaborate_static_type(ctx, ty)?;
	let ty_value = ty.clone().evaluate_in(&ctx.environment);
	let argument =
		verify_static(&mut ctx.amplify(grade).erase_if(grade == 0.into()), argument, ty_value.clone())?;
	// TODO: Lazy evaluation.
	let argument_value = argument.clone().evaluate_in(&ctx.environment);
	let parameters = tail.parameters;
	let tail_b = {
		let mut context = ctx.extend_static(
			parameters[0],
			false,
			grade * (ctx.fragment as usize).into(),
			ty_c,
			ty_value,
			argument_value,
		);
		let result = elaborate_tail(&mut context, *tail.body, tail_a)?;
		context.free().map_err(|e| e.at(expr_range))?;
		result
	};
	Ok(produce_let(grade, ty, argument, parameters, tail_b))
}

fn elaborate_dynamic_let<A, B>(
	ctx: &mut Context,
	expr_range: (usize, usize),
	PreLet { grade, ty, argument, tail }: PreLet,
	tail_a: A,
	elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
	produce_let: impl FnOnce(usize, DynamicTerm, KindTerm, DynamicTerm, [Option<Name>; 1], B) -> B,
) -> Result<B, ElaborationError> {
	let grade = grade.unwrap_or_else(|| if tail.parameter().is_some() { 1 } else { 0 }.into());
	let Cost::Fin(grade) = grade else {
		panic!();
	};
	let (ty, argument_kind) = elaborate_dynamic_type(ctx, ty)?;
	let ty_value = ty.clone().evaluate_in(&ctx.environment);
	let argument = verify_dynamic(&mut ctx.amplify(grade).erase_if(grade == 0), argument, ty_value.clone())?;
	// TODO: Lazy evaluation.
	let argument_value = argument.clone().evaluate_in(&ctx.environment);
	let parameters = tail.parameters;
	let tail_b = {
		let mut context = ctx.extend_dynamic(
			parameters[0],
			false,
			(grade * ctx.fragment as usize).into(),
			ty_value,
			argument_kind.clone(),
			argument_value,
		);
		let result = elaborate_tail(&mut context, *tail.body, tail_a)?;
		context.free().map_err(|e| e.at(expr_range))?;
		result
	};

	let argument_kind = argument_kind.unevaluate_in(ctx.len());

	Ok(produce_let(grade, ty, argument_kind, argument, parameters, tail_b))
}

struct PreSgLet {
	grade: usize,
	argument: Expression,
	tail: Binder<Box<Expression>, 2>,
}

fn elaborate_static_sg_let<A, B>(
	ctx: &mut Context,
	expr_range: (usize, usize),
	PreSgLet { grade, argument, tail }: PreSgLet,
	tail_a: A,
	elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
	produce_let: impl FnOnce(usize, StaticTerm, [Option<Name>; 2], B) -> B,
) -> Result<B, ElaborationError> {
	let (tm, ty) = synthesize_static(&mut ctx.amplify(grade).erase_if(grade == 0), argument)?;
	let StaticValue::IndexedSum { base_copy, base, family_copy, family } = ty else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr_range));
	};
	let parameters = tail.parameters;
	// This evaluates tm twice; may want to factor this out if convenient.
	let basepoint = StaticTerm::SgField(tm.clone().into(), Field::Base).evaluate_in(&ctx.environment);
	let fiberpoint = StaticTerm::SgField(tm.clone().into(), Field::Fiber).evaluate_in(&ctx.environment);
	let tail_b = {
		let mut ctx = ctx.extend_static(
			parameters[0],
			false,
			(grade * ctx.fragment as usize).into(),
			base_copy,
			(*base).clone(),
			basepoint.clone(),
		);
		let result = {
			let fragment = ctx.fragment;
			let mut ctx = ctx.extend_static(
				parameters[1],
				false,
				(grade * fragment as usize).into(),
				family_copy,
				family.evaluate_with([basepoint]),
				fiberpoint,
			);
			let result = elaborate_tail(&mut ctx, *tail.body, tail_a)?;
			ctx.free().map_err(|e| e.at(expr_range))?;
			result
		};
		ctx.free().map_err(|e| e.at(expr_range))?;
		result
	};

	Ok(produce_let(grade, tm, parameters, tail_b))
}

fn elaborate_dynamic_sg_let<A, B>(
	ctx: &mut Context,
	expr_range: (usize, usize),
	PreSgLet { grade, argument, tail }: PreSgLet,
	tail_a: A,
	elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
	produce_let: impl FnOnce(usize, [Box<KindTerm>; 2], DynamicTerm, [Option<Name>; 2], B) -> B,
) -> Result<B, ElaborationError> {
	let (tm, ty, _) = synthesize_dynamic(&mut ctx.amplify(grade).erase_if(grade == 0), argument)?;
	let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = ty else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr_range));
	};
	let parameters = tail.parameters;
	// This evaluates tm twice; may want to factor this out if convenient.
	let basepoint =
		DynamicTerm::SgField { scrutinee: tm.clone().into(), field: Field::Base }.evaluate_in(&ctx.environment);
	let fiberpoint = DynamicTerm::SgField { scrutinee: tm.clone().into(), field: Field::Fiber }
		.evaluate_in(&ctx.environment);
	let tail_b = {
		let mut ctx = ctx.extend_dynamic(
			parameters[0],
			false,
			(grade * ctx.fragment as usize).into(),
			(*base).clone(),
			(*base_kind).clone(),
			basepoint.clone(),
		);
		let result = {
			let fragment = ctx.fragment;
			let mut ctx = ctx.extend_dynamic(
				parameters[1],
				false,
				(grade * fragment as usize).into(),
				family.evaluate_with([basepoint]),
				(*family_kind).clone(),
				fiberpoint,
			);
			let result = elaborate_tail(&mut ctx, *tail.body, tail_a)?;
			ctx.free().map_err(|e| e.at(expr_range))?;
			result
		};
		ctx.free().map_err(|e| e.at(expr_range))?;
		result
	};

	let kinds = [base_kind, family_kind].map(|x| x.unevaluate_in(ctx.len()).into());

	Ok(produce_let(grade, kinds, tm, parameters, tail_b))
}
