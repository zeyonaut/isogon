use std::{
	ops::{Deref, DerefMut},
	rc::Rc,
};

use lasso::{Rodeo};

use crate::{
	delta::{
		common::{bind, Closure, Field, Index, Level, Name},
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

use super::{unelaborate::Unelaborate, unparse::print};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(
	source: &str,
	lexed_source: &LexedSource,
	program: ParsedProgram,
	interner: &Rodeo,
) -> (DynamicTerm, DynamicValue) {
	// TODO: Offer option to choose fragment, rather than force fragment to be 1.
	match synthesize_dynamic(&mut Context::empty(), program.expr, program.fragment) {
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

pub fn display_error(kind: ElaborationErrorKind, interner: &Rodeo) -> String {
	match kind {
		ElaborationErrorKind::StaticBidirectionalMismatch { synthesized, expected } => {
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner);
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner);
			format!("elaboration error: type mismatch\nexpected: {}\nfound: {}", ty_ex, ty_sy)
		}
		ElaborationErrorKind::DynamicBidirectionalMismatch { synthesized, expected } => {
			let mut ty_sy = String::new();
			print(&synthesized.unelaborate(), &mut ty_sy, interner);
			let mut ty_ex = String::new();
			print(&expected.unelaborate(), &mut ty_ex, interner);
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
	DynamicUniverse,
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
	grade: Option<usize>,
	ty: ContextType,
}

impl ContextEntry {
	pub fn new(is_crisp: bool, grade: Option<usize>, ty: ContextType) -> Self { Self { is_crisp, grade, ty } }
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
	fn drop(&mut self) { self.old_lock.map(|old_lock| self.context.lock = old_lock); }
}

pub struct AmplifiedContext<'c> {
	context: &'c mut Context,
}

impl<'c> AmplifiedContext<'c> {
	fn new(ctx: &'c mut Context, amplifier: Option<usize>) -> Self {
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

	#[must_use]
	fn free(self) -> Result<(), ElaborationErrorKind> {
		let grade = self.tys.last().unwrap().1.grade;
		if let Some(grade) = grade {
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

pub struct Context {
	lock: usize,
	amplifiers: Vec<(usize, Option<usize>)>,
	environment: Environment,
	tys: Vec<(Option<Name>, ContextEntry)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { lock: 0, amplifiers: Vec::new(), environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level { Level(self.environment.0.len()) }

	// Uses a resource.
	#[must_use]
	fn take_index(&mut self, index: usize, fragment: u8) -> Result<(), ElaborationErrorKind> {
		let level = self.tys.len() - (index + 1);

		if !self.tys[level].1.is_crisp && level < self.lock {
			return Err(ElaborationErrorKind::UsedNonCrispLockedVariable);
		}

		let mut usage = Some(fragment as usize);
		// Skip this for fragment 0, as 0 is absorbing under multiplication.
		if usage != Some(0) {
			for (len, amplifier) in self.amplifiers.iter().rev() {
				if level < *len {
					match (&mut usage, amplifier) {
						(usage, Some(0)) => {
							*usage = Some(0);
							break;
						}
						(usage, None) => *usage = None,
						(None, _) => (),
						(Some(usage), Some(amplifier)) => *usage *= amplifier,
					}
				} else {
					break;
				}
			}
		}
		match (usage, self.tys[level].1.grade.as_mut()) {
			(_, None) => (),
			(None, Some(_)) => return Err(ElaborationErrorKind::RanOutOfVariableUses),
			(Some(amplifier), Some(grade)) => {
				*grade = grade.checked_sub(amplifier).ok_or(ElaborationErrorKind::RanOutOfVariableUses)?;
			}
		}
		Ok(())
	}

	pub fn lock_if<'c>(&'c mut self, should_lock: bool) -> LockedContext<'c> {
		LockedContext::new(self, should_lock)
	}

	pub fn amplify<'c>(&'c mut self, amplifier: impl Into<Option<usize>>) -> AmplifiedContext<'c> {
		AmplifiedContext::new(self, amplifier.into())
	}

	pub fn bind_static<'c>(
		&'c mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Option<usize>,
		ty: StaticValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(is_crisp, grade, ContextType::Static(ty)),
			Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))),
		)
	}

	pub fn bind_dynamic<'c>(
		&'c mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Option<usize>,
		ty: DynamicValue,
		kind: KindValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(is_crisp, grade, ContextType::Dynamic(ty, kind)),
			Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))),
		)
	}

	pub fn extend_static<'c>(
		&'c mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Option<usize>,
		ty: StaticValue,
		value: StaticValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(is_crisp, grade, ContextType::Static(ty)),
			Value::Static(value),
		)
	}

	pub fn extend_dynamic<'c>(
		&'c mut self,
		name: Option<Name>,
		is_crisp: bool,
		grade: Option<usize>,
		ty: DynamicValue,
		kind: KindValue,
		value: DynamicValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(is_crisp, grade, ContextType::Dynamic(ty, kind)),
			Value::Dynamic(value),
		)
	}
}

fn synthesize_static(
	ctx: &mut Context,
	expr: Expression,
	fragment: u8,
) -> Result<(StaticTerm, StaticValue), ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match preterm {
		// Variables.
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in ctx.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Static(ty) = &entry.ty {
						let result = (StaticTerm::Variable(Some(name), Index(i)), ty.clone());
						ctx.take_index(i, fragment).map_err(|e| e.at(expr.range))?;
						break 'var result;
					} else {
						return Err(ElaborationErrorKind::ExpectedStaticFoundDynamicVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		},

		// Let-expressions.
		Preterm::Let { grade, ty, argument, tail } => {
			let ty = verify_static(ctx, *ty, 0, StaticValue::Universe)?;
			let ty_value = ty.clone().evaluate_in(&ctx.environment);
			let argument = verify_static(
				&mut ctx.amplify(grade),
				*argument,
				fragment * (grade > 0) as u8,
				ty_value.clone(),
			)?;
			// TODO: Lazy evaluation.
			let argument_value = argument.clone().evaluate_in(&ctx.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty) = {
				let mut context = ctx.extend_static(
					parameters[0],
					false,
					(grade * fragment as usize).into(),
					ty_value,
					argument_value,
				);
				let result = synthesize_static(&mut context, *tail.body, fragment)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};
			(
				StaticTerm::Let { grade, ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) },
				tail_ty,
			)
		}

		// Quoting.
		Preterm::SwitchLevel(quotee) => {
			let (quotee, quotee_ty, kind) = synthesize_dynamic(ctx, *quotee, fragment)?;
			(StaticTerm::Quote(bx!(quotee)), StaticValue::Lift { ty: quotee_ty.into(), kind: kind.into() })
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if fragment == 0 => {
			let base = verify_static(ctx, *base, 0, StaticValue::Universe)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let [parameter] = family.parameters;
			let family = {
				let mut context = ctx.bind_static(parameter, false, 0.into(), base_value);
				let family = verify_static(&mut context, *family.body, 0, StaticValue::Universe)?;
				context.free().map_err(|e| e.at(expr.range))?;
				family
			};
			(StaticTerm::Pi(grade.into(), bx!(base), bind([parameter], family)), StaticValue::Universe)
		}
		Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::Call { callee, argument } => {
			let (callee, scrutinee_ty) = synthesize_static(ctx, *callee, fragment)?;
			let StaticValue::IndexedProduct(grade, base, family) = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument =
				verify_static(&mut ctx.amplify(grade), *argument, fragment * (grade > 0) as u8, (*base).clone())?;
			(
				StaticTerm::Apply { scrutinee: bx!(callee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&ctx.environment)]),
			)
		}

		// Dependent pairs.
		Preterm::Sg { base, family } => {
			let base = verify_static(ctx, *base, 0, StaticValue::Universe)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let [parameter] = family.parameters;
			let family = {
				let mut context = ctx.bind_static(parameter, false, 0.into(), base_value);
				let family = verify_static(&mut context, *family.body, 0, StaticValue::Universe)?;
				context.free().map_err(|e| e.at(expr.range))?;
				family
			};
			(StaticTerm::Sg(bx!(base), bind([parameter], family)), StaticValue::Universe)
		}
		Preterm::Pair { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::SgLet { grade, argument, tail } => {
			let (tm, ty) = synthesize_static(&mut ctx.amplify(grade), *argument, fragment)?;
			let StaticValue::IndexedSum(base, family) = ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
			};
			let parameters = tail.parameters;
			// This evaluates tm twice; may want to factor this out if convenient.
			let basepoint = StaticTerm::SgField(tm.clone().into(), Field::Base).evaluate_in(&ctx.environment);
			let fiberpoint = StaticTerm::SgField(tm.clone().into(), Field::Fiber).evaluate_in(&ctx.environment);
			let (tail, tail_ty) = {
				let mut ctx = ctx.extend_static(
					parameters[0],
					false,
					(grade * fragment as usize).into(),
					(*base).clone(),
					basepoint.clone(),
				);
				let result = {
					let mut ctx = ctx.extend_static(
						parameters[0],
						false,
						(grade * fragment as usize).into(),
						family.evaluate_with([basepoint]),
						fiberpoint,
					);
					let result = synthesize_static(&mut ctx, *tail.body, fragment)?;
					result
				};
				ctx.free().map_err(|e| e.at(expr.range))?;
				result
			};

			(StaticTerm::SgLet { grade, argument: tm.into(), tail: bind(parameters, tail) }, tail_ty)
		}

		// Generic type formers.
		Preterm::Former(former, arguments) => match former {
			// Types and universe indices.
			Former::Universe if fragment == 0 && arguments.is_empty() =>
				(StaticTerm::Universe, StaticValue::Universe),
			Former::Copy if fragment == 0 && arguments.is_empty() => (StaticTerm::Cpy, StaticValue::Universe),
			Former::Repr if fragment == 0 && arguments.is_empty() => (StaticTerm::Repr, StaticValue::Universe),

			// Quoting.
			Former::Lift => {
				let [liftee] = arguments.try_into().unwrap();
				let (liftee, kind) = elaborate_dynamic_type(ctx, liftee)?;
				(
					StaticTerm::Lift { liftee: liftee.into(), kind: kind.unevaluate_in(ctx.len()).into() },
					StaticValue::Universe,
				)
			}

			// Repeated programs.
			Former::Exp(grade) => {
				let [ty] = arguments.try_into().unwrap();
				let ty = verify_static(ctx, ty, 0, StaticValue::Universe)?;
				(StaticTerm::Exp(grade, ty.into()), StaticValue::Universe)
			}

			// Enumerated numbers.
			Former::Enum(card) if arguments.is_empty() => (StaticTerm::Enum(card), StaticValue::Universe),

			// Natural numbers.
			Former::Nat if arguments.is_empty() => (StaticTerm::Nat, StaticValue::Universe),

			// Invalid former.
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},

		// Generic term constructors.
		Preterm::Constructor(constructor, arguments) => match constructor {
			// Universe indices.
			Constructor::Cpy(c) if fragment == 0 && arguments.is_empty() =>
				(StaticTerm::CpyValue(c), StaticValue::Cpy),
			Constructor::CpyMax if fragment == 0 => {
				let [a, b] = arguments.try_into().unwrap();
				let a = verify_static(ctx, a, 0, StaticValue::Cpy)?;
				let b = verify_static(ctx, b, 0, StaticValue::Cpy)?;
				(StaticTerm::CpyMax(bx!(a), bx!(b)), StaticValue::Cpy)
			}
			Constructor::ReprAtom(r) if fragment == 0 && arguments.is_empty() =>
				(StaticTerm::ReprAtom(r), StaticValue::ReprType),
			Constructor::ReprPair if fragment == 0 => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(ctx, r0, 0, StaticValue::ReprType)?;
				let r1 = verify_static(ctx, r1, 0, StaticValue::ReprType)?;
				(StaticTerm::ReprPair(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}

			// Repeated programs.
			Constructor::Exp(grade) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty) = synthesize_static(ctx, tm, 0)?;
				(StaticTerm::Exp(grade, tm.into()), StaticValue::Exp(grade, ty.into()))
			}

			// Enumerated numbers.
			Constructor::Enum(k, v) if arguments.is_empty() =>
				(StaticTerm::EnumValue(k, v), StaticValue::Enum(k)),

			// Natural numbers.
			Constructor::Num(n) if arguments.is_empty() => (StaticTerm::Num(n), StaticValue::Nat),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_static(ctx, prev, fragment, StaticValue::Nat)?;
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
			Projector::Field(field) if fragment == 0 => {
				let (scrutinee, scrutinee_ty) = synthesize_static(ctx, *scrutinee, 0)?;
				let StaticValue::IndexedSum(base, family) = scrutinee_ty else {
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
		Preterm::Split { scrutinee, motive, cases } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(ctx, *scrutinee, fragment)?;
			let scrutinee_value = scrutinee.clone().evaluate_in(&ctx.environment);
			match scrutinee_ty {
				StaticValue::Enum(card) => {
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == card as _)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					let motive_term = verify_static(
						&mut ctx.bind_static(motive_parameter, false, 0.into(), StaticValue::Enum(card)),
						*motive.body,
						0,
						StaticValue::Universe,
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
							fragment,
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
					let motive = verify_static(
						&mut ctx.bind_static(motive_parameter, false, 0.into(), StaticValue::Nat),
						*motive.body,
						fragment,
						StaticValue::Universe,
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
						verify_static(ctx, case_nil, fragment, motive_value.evaluate_with([StaticValue::Num(0)]))?;
					let case_suc = {
						// Effectively disallow using nontrivial resources in recursive case.
						let mut ctx = ctx.amplify(None);
						let mut ctx = ctx.bind_static(index, false, None, StaticValue::Nat);
						let index_level = ctx.len().index(0);
						let result = {
							let mut ctx = ctx.bind_static(
								witness,
								false,
								(1 * fragment as usize).into(),
								motive_value.evaluate_with([(index, index_level).into()]),
							);
							let result = verify_static(
								&mut ctx,
								case_suc,
								fragment,
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
	fragment: u8,
	ty: StaticValue,
) -> Result<StaticTerm, ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match (preterm, ty) {
		// Quoted programs.
		(Preterm::SwitchLevel(quotee), ty) => {
			let StaticValue::Lift { ty: liftee, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			let quotee = verify_dynamic(ctx, *quotee, fragment, liftee)?;
			StaticTerm::Quote(bx!(quotee))
		}

		// Dependent functions.
		(Preterm::Lambda { grade, body }, StaticValue::IndexedProduct(grade_v, base, family)) => {
			(grade * fragment as usize == grade_v * fragment as usize)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_v).at(expr.range))?;
			let parameters = body.parameters;
			let mut context =
				ctx.bind_static(parameters[0], false, (grade * fragment as usize).into(), base.as_ref().clone());
			let basepoint_level = context.len().index(0);
			let body = verify_static(
				&mut context,
				*body.body,
				fragment,
				family.evaluate_with([(parameters[0], basepoint_level).into()]),
			)?;
			context.free().map_err(|e| e.at(expr.range))?;
			StaticTerm::Function(grade, bind(parameters, body))
		}

		// Dependent pairs.
		(Preterm::Pair { basepoint, fiberpoint }, StaticValue::IndexedSum(base, family)) => {
			let basepoint = verify_static(ctx, *basepoint, fragment, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&ctx.environment);
			let fiberpoint = verify_static(ctx, *fiberpoint, fragment, family.evaluate_with([basepoint_value]))?;
			StaticTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
		}

		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(ctx, term.at(expr.range), fragment)?;
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
	fragment: u8,
) -> Result<(DynamicTerm, DynamicValue, KindValue), ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match preterm {
		// Variables.
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in ctx.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Dynamic(ty, kind) = &entry.ty {
						let result = (DynamicTerm::Variable(Some(name), Index(i)), ty.clone(), kind.clone());
						ctx.take_index(i, fragment).map_err(|e| e.at(expr.range))?;
						break 'var result;
					} else {
						return Err(ElaborationErrorKind::ExpectedDynamicFoundStaticVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		},

		// Let-expressions.
		Preterm::Let { grade, ty, argument, tail } => {
			let (ty, base_kind) = elaborate_dynamic_type(ctx, *ty)?;
			let ty_value = ty.clone().evaluate_in(&ctx.environment);
			let argument = verify_dynamic(
				&mut ctx.amplify(grade),
				*argument,
				fragment * (grade > 0) as u8,
				ty_value.clone(),
			)?;
			// TODO: Lazy evaluation.
			let argument_value = argument.clone().evaluate_in(&ctx.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty, tail_kind) = {
				let mut context = ctx.extend_dynamic(
					parameters[0],
					false,
					(grade * fragment as usize).into(),
					ty_value,
					base_kind,
					argument_value,
				);
				let result = synthesize_dynamic(&mut context, *tail.body, fragment)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};

			(
				DynamicTerm::Let { grade, ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) },
				tail_ty,
				tail_kind,
			)
		}

		// Splicing.
		Preterm::SwitchLevel(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, kind }) = synthesize_static(ctx, *splicee, fragment)?
			else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*kind).clone())
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if fragment == 0 => {
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
			let Ok(family_kind) = family_kind.try_unevaluate_in(ctx.len()).into() else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Pi {
					grade: grade.into(),
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
			let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(ctx, *callee, fragment)?;
			let DynamicValue::IndexedProduct { grade, base, family_kind, family, .. } = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument = verify_dynamic(
				&mut ctx.amplify(grade),
				*argument,
				fragment * (grade > 0) as u8,
				(*base).clone(),
			)?;
			let argument_value = argument.clone().evaluate_in(&ctx.environment);
			(
				DynamicTerm::Apply {
					scrutinee: scrutinee.into(),
					argument: argument.into(),
					family_kind: Some(family_kind.unevaluate_in(ctx.len()).into()),
				},
				family.evaluate_with([argument_value]),
				(*family_kind).clone(),
			)
		}

		// Dependent pairs.
		Preterm::Sg { base, family } => {
			let (base, base_kind) = elaborate_dynamic_type(ctx, *base)?;
			let base_value = base.clone().evaluate_in(&ctx.environment);
			let parameters = family.parameters;
			let (family, family_kind) = {
				let mut context = ctx.bind_dynamic(parameters[0], false, 0.into(), base_value, base_kind.clone());
				let result = elaborate_dynamic_type(&mut context, *family.body)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};

			let kind = KindValue::pair(base_kind.clone(), family_kind.clone());

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let Ok(family_kind) = family_kind.try_unevaluate_in(ctx.len()).into() else {
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
		Preterm::SgLet { grade, argument, tail } => {
			let (tm, ty, _) = synthesize_dynamic(&mut ctx.amplify(grade), *argument, fragment)?;
			let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
			};
			let parameters = tail.parameters;
			// This evaluates tm twice; may want to factor this out if convenient.
			let basepoint = DynamicTerm::SgField { scrutinee: tm.clone().into(), field: Field::Base }
				.evaluate_in(&ctx.environment);
			let fiberpoint = DynamicTerm::SgField { scrutinee: tm.clone().into(), field: Field::Fiber }
				.evaluate_in(&ctx.environment);
			let (tail, tail_ty, kind) = {
				let mut ctx = ctx.extend_dynamic(
					parameters[0],
					false,
					(grade * fragment as usize).into(),
					(*base).clone(),
					(*base_kind).clone(),
					basepoint.clone(),
				);
				let result = {
					let mut ctx = ctx.extend_dynamic(
						parameters[0],
						false,
						(grade * fragment as usize).into(),
						family.evaluate_with([basepoint]),
						(*family_kind).clone(),
						fiberpoint,
					);
					let result = synthesize_dynamic(&mut ctx, *tail.body, fragment)?;
					result
				};
				ctx.free().map_err(|e| e.at(expr.range))?;
				result
			};

			(DynamicTerm::SgLet { grade, argument: tm.into(), tail: bind(parameters, tail) }, tail_ty, kind)
		}

		// Generic type formers.
		Preterm::Former(former, arguments) => match former {
			// Types.
			Former::Universe if fragment == 0 => {
				let [copy, repr] = arguments.try_into().unwrap();
				let copy = verify_static(ctx, copy, 0, StaticValue::Cpy)?;
				let repr = verify_static(ctx, repr, 0, StaticValue::ReprType)?;
				(
					DynamicTerm::Universe { kind: KindTerm { copy, repr }.into() },
					DynamicValue::Universe { kind: KindValue::ty().into() },
					KindValue::ty(),
				)
			}

			// Repeated programs.
			Former::Exp(grade) => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, kind) = elaborate_dynamic_type(ctx, ty)?;
				(
					DynamicTerm::Exp(grade, ty.into()),
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
				let x = verify_dynamic(ctx, x, 0, ty_value.clone())?;
				let y = verify_dynamic(ctx, y, 0, ty_value.clone())?;
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
			Constructor::Exp(grade) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm, fragment)?;
				(DynamicTerm::Exp(grade, tm.into()), DynamicValue::Exp(grade, ty.into()), kind.exp(grade))
			}

			// Enumerated numbers.
			Constructor::Enum(k, v) if arguments.is_empty() =>
				(DynamicTerm::EnumValue(k, v), DynamicValue::Enum(k), KindValue::enu()),

			// Natural numbers.
			Constructor::Num(n) if arguments.is_empty() =>
				(DynamicTerm::Num(n), DynamicValue::Nat, KindValue::nat()),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_dynamic(ctx, prev, fragment, DynamicValue::Nat)?;
				if let DynamicTerm::Num(p) = prev {
					(DynamicTerm::Num(p + 1), DynamicValue::Nat, KindValue::nat())
				} else {
					(DynamicTerm::Suc(prev.into()), DynamicValue::Nat, KindValue::nat())
				}
			}

			// Wrappers.
			Constructor::Bx => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm, fragment)?;
				(
					DynamicTerm::BxValue(bx!(tm)),
					DynamicValue::Bx { inner: ty.into(), kind: kind.into() },
					KindValue::ptr(),
				)
			}
			Constructor::Wrap => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, kind) = synthesize_dynamic(ctx, tm, fragment)?;
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
			// Dependent pairs.
			Projector::Field(field) if fragment == 0 => {
				let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(ctx, *scrutinee, 0)?;
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
				let (tm, DynamicValue::Bx { inner: ty, kind }, _) =
					synthesize_dynamic(ctx, *scrutinee, fragment)?
				else {
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
				let (tm, DynamicValue::Wrap { inner: ty, kind }, _) =
					synthesize_dynamic(ctx, *scrutinee, fragment)?
				else {
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
		Preterm::Split { scrutinee, motive, cases } => {
			let (scrutinee, scrutinee_ty, _) = synthesize_dynamic(ctx, *scrutinee, fragment)?;
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
						new_cases.push(verify_dynamic(
							ctx,
							case,
							fragment,
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

				// Paths.
				DynamicValue::Id { kind, space, left, right } => {
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
						let mut context = ctx.bind_dynamic(v, false, 0.into(), (*space).clone(), (*kind).clone());
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
						fragment,
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
						verify_dynamic(ctx, case_nil, fragment, motive.evaluate_with([DynamicValue::Num(0)]))?;
					// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
					let case_suc = {
						// Effectively disallow using nontrivial resources in recursive case.
						let mut ctx = ctx.amplify(None);
						// NOTE: Unrestricted usage is only "safe" because we're approximating Nat with a finite type.
						// For nontrivial Nat, we may wish to enclose the index with a thunk.
						let mut ctx =
							ctx.bind_dynamic(index, false, None.into(), DynamicValue::Nat, KindValue::nat());
						let index_level = ctx.len().index(0);
						let result = {
							let mut ctx = ctx.bind_dynamic(
								witness,
								false,
								(1 * fragment as usize).into(),
								motive.evaluate_with([(index, index_level).into()]),
								motive_kind.clone(),
							);
							let result = verify_dynamic(
								&mut ctx,
								case_suc,
								fragment,
								motive.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(Rc::new(
									DynamicNeutral::Variable(index, index_level).into(),
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

		// Synthesis failure.
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeDynamic.at(expr.range)),
	})
}

fn verify_dynamic(
	ctx: &mut Context,
	expr: Expression,
	fragment: u8,
	ty: DynamicValue,
) -> Result<DynamicTerm, ElaborationError> {
	let ParsedPreterm(preterm) = expr.preterm;
	Ok(match (preterm, ty) {
		// Dependent functions.
		(
			Preterm::Lambda { grade, body },
			DynamicValue::IndexedProduct { grade: grade_t, base, base_kind, family, .. },
		) => {
			(grade * fragment as usize == grade_t * fragment as usize)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_t).at(expr.range))?;
			let parameters = body.parameters;
			let mut context = ctx.bind_dynamic(
				parameters[0],
				false,
				(grade * fragment as usize).into(),
				base.as_ref().clone(),
				(*base_kind).clone(),
			);
			let basepoint_level = context.len().index(0);
			let body = verify_dynamic(
				&mut context,
				*body.body,
				fragment,
				family.evaluate_with([(parameters[0], basepoint_level).into()]),
			)?;
			context.free().map_err(|e| e.at(expr.range))?;
			DynamicTerm::Function { grade, body: bind(parameters, body) }
		}

		// Dependent pairs.
		(Preterm::Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(ctx, *basepoint, fragment, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&ctx.environment);
			let fiberpoint =
				verify_dynamic(ctx, *fiberpoint, fragment, family.evaluate_with([basepoint_value]))?;
			DynamicTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
		}

		// Paths.
		(Preterm::Constructor(Constructor::Refl, tms), ty) => {
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
			let tm = verify_dynamic(ctx, tm, fragment, ty.as_ref().clone())?;
			DynamicTerm::BxValue(bx!(tm))
		}
		(Preterm::Constructor(Constructor::Wrap, tms), ty) => {
			let DynamicValue::Wrap { inner: ty, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Wrap).at(expr.range));
			};
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(ctx, tm, fragment, ty.as_ref().clone())?;
			DynamicTerm::WrapValue(bx!(tm))
		}

		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty, _) = synthesize_dynamic(ctx, term.at(expr.range), fragment)?;
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

fn elaborate_dynamic_type(
	ctx: &mut Context,
	expr: Expression,
) -> Result<(DynamicTerm, KindValue), ElaborationError> {
	let expr_range = expr.range;
	let (term, DynamicValue::Universe { kind }, _) = synthesize_dynamic(ctx, expr, 0)? else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::DynamicUniverse).at(expr_range));
	};
	Ok((term, (*kind).clone()))
}
