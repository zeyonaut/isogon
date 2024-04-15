use std::{
	ops::{Deref, DerefMut},
	rc::Rc,
};

use lasso::Resolver;

use super::{unelaborate::Unelaborate, unparse::print};
use crate::delta::{
	common::{bind, Binder, Cost, Cpy, Field, Index, Label, Level, Name},
	ir::{
		presyntax::{
			Constructor, Expression, Former, ParsedLabel, ParsedPreterm, ParsedProgram, Pattern, Preterm,
			Projector,
		},
		semantics::{DynamicNeutral, DynamicValue, Environment, KindValue, StaticNeutral, StaticValue, Value},
		source::LexedSource,
		syntax::{DynamicTerm, KindTerm, StaticTerm},
	},
	op::{
		conversion::Conversion,
		evaluate::{Evaluate, EvaluateWith},
		parse::report_line_error,
		unevaluate::Unevaluate,
	},
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(
	source: &str,
	lexed_source: &LexedSource,
	program: ParsedProgram,
	interner: &impl Resolver,
) -> (DynamicTerm, DynamicValue) {
	match Context::empty(if program.fragment == 0 { Fragment::Logical } else { Fragment::Material })
		.synthesize_dynamic(program.expr)
	{
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
	WrongArity,
	InvalidArgumentCount,
	InvalidStaticUniverse,
	InvalidGrade,
}

impl ElaborationErrorKind {
	fn at(self, range: (usize, usize)) -> ElaborationError { ElaborationError { range, kind: self } }
}

#[derive(Clone, Debug)]
pub enum ContextType {
	Static(StaticValue, Cpy),
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

pub struct ExtendedContext<'c, T, const N: usize> {
	context: &'c mut Context,
	binder: Binder<ParsedLabel, T, N>,
	count: usize,
}

impl<'c, T, const N: usize> ExtendedContext<'c, T, N> {
	fn new(context: &'c mut Context, binder: Binder<ParsedLabel, T, N>) -> Self {
		Self { context, binder, count: 0 }
	}

	pub fn push(&mut self, entry: ContextEntry, value: Value) {
		self.context.tys.push((self.binder.parameters[self.count].label, entry));
		self.context.environment.push(value);
		self.count += 1;
	}

	pub fn bind_static(mut self, is_crisp: bool, grade: Cost, copy: Cpy, ty: StaticValue) -> Self {
		let grade = grade * (self.context.fragment as usize).into();
		self.push(
			ContextEntry::new(
				is_crisp,
				if copy == Cpy::Nt || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Static(ty, copy),
			),
			Value::Static(StaticValue::Neutral(StaticNeutral::Variable(
				self.binder.parameters[self.count].label,
				self.context.len(),
			))),
		);
		self
	}

	pub fn bind_static_with(
		self,
		is_crisp: bool,
		grade: Cost,
		copy: Cpy,
		ty: impl FnOnce(&Context) -> StaticValue,
	) -> Self {
		let ty = ty(self.context);
		self.bind_static(is_crisp, grade, copy, ty)
	}

	pub fn bind_dynamic(mut self, is_crisp: bool, grade: Cost, kind: KindValue, ty: DynamicValue) -> Self {
		let grade = grade * (self.context.fragment as usize).into();
		self.push(
			ContextEntry::new(
				is_crisp,
				if !kind.copy.is_trivial() || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Dynamic(ty, kind),
			),
			Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(
				self.binder.parameters[self.count].label,
				self.context.len(),
			))),
		);
		self
	}

	pub fn bind_dynamic_with(
		self,
		is_crisp: bool,
		grade: Cost,
		kind: KindValue,
		ty: impl FnOnce(&Context) -> DynamicValue,
	) -> Self {
		let ty = ty(self.context);
		self.bind_dynamic(is_crisp, grade, kind, ty)
	}

	pub fn alias_static(
		mut self,
		is_crisp: bool,
		grade: Cost,
		copy: Cpy,
		ty: StaticValue,
		value: StaticValue,
	) -> Self {
		let grade = grade * (self.context.fragment as usize).into();
		self.push(
			ContextEntry::new(
				is_crisp,
				if copy == Cpy::Nt || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Static(ty, copy),
			),
			Value::Static(value),
		);
		self
	}

	pub fn alias_dynamic(
		mut self,
		is_crisp: bool,
		grade: Cost,
		kind: KindValue,
		ty: DynamicValue,
		value: DynamicValue,
	) -> Self {
		let grade = grade * (self.context.fragment as usize).into();
		self.push(
			ContextEntry::new(
				is_crisp,
				if !kind.copy.is_trivial() || grade == 0.into() { grade } else { Cost::Inf },
				ContextType::Dynamic(ty, kind),
			),
			Value::Dynamic(value),
		);
		self
	}

	fn map_extra<O, I>(
		self,
		action: impl FnOnce(&mut Context, T) -> Result<(O, I), ElaborationError>,
	) -> Result<(Binder<Label, O, N>, I), ElaborationError> {
		self.map(action).map(|x| x.retract())
	}

	fn map<O>(
		self,
		action: impl FnOnce(&mut Context, T) -> Result<O, ElaborationError>,
	) -> Result<Binder<Label, O, N>, ElaborationError> {
		assert_eq!(self.count, self.binder.parameters.len(), "underextended context");
		let result = action(self.context, self.binder.body)?;
		for p in self.binder.parameters.iter().rev() {
			let grade = self.context.tys.last().unwrap().1.grade;
			if let Cost::Fin(grade) = grade {
				(grade == 0)
					.then_some(())
					.ok_or(ElaborationErrorKind::VariableHasUsesLeft(grade))
					.map_err(|e| e.at((p.locus, p.locus + 1)))?
			}
			self.context.tys.pop();
			self.context.environment.pop();
		}
		Ok(bind(self.binder.parameters.map(|x| x.label), result))
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

	fn var<T: From<(Label, Level)>>(&self, index: usize) -> T {
		let level = self.len().index(index);
		(self.tys[level.0].0, level).into()
	}
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

	pub fn extend<T, const N: usize>(
		&mut self,
		binder: Binder<ParsedLabel, T, N>,
	) -> ExtendedContext<'_, T, N> {
		ExtendedContext::new(self, binder)
	}

	fn synthesize_static(
		&mut self,
		expr: Expression,
	) -> Result<(StaticTerm, StaticValue, Cpy), ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match preterm {
			// Variables.
			Preterm::Variable(name) => 'var: {
				for (i, (name_1, entry)) in self.tys.iter().rev().enumerate() {
					if &Some(name) == name_1 {
						if let ContextType::Static(ty, c) = &entry.ty {
							let result = (StaticTerm::Variable(Some(name), Index(i)), ty.clone(), *c);
							self.take_index(i).map_err(|e| e.at(expr.range))?;
							break 'var result;
						} else {
							return Err(ElaborationErrorKind::ExpectedStaticFoundDynamicVariable.at(expr.range));
						}
					}
				}
				return Err(ElaborationErrorKind::NotInScope.at(expr.range));
			}

			// Let-expressions.
			Preterm::Let { is_meta: true, grade, ty, argument, tail } => self.elaborate_static_let(
				PreLet { grade, ty: *ty, argument: *argument, tail },
				(),
				|ctx, tail_body, ()| ctx.synthesize_static(tail_body),
				|grade, ty, argument, tail| {
					let (tail, tail_ty, c) = tail.retract2();
					(
						StaticTerm::Let { grade, ty: ty.into(), argument: argument.into(), tail: tail.map_into() },
						tail_ty,
						c,
					)
				},
			)?,

			// Quoting.
			Preterm::SwitchLevel(quotee) => {
				let (quotee, quotee_ty, kind) = self.synthesize_dynamic(*quotee)?;
				(
					StaticTerm::Quote(quotee.into()),
					StaticValue::Lift { ty: quotee_ty, kind: kind.into() },
					Cpy::Nt,
				)
			}

			// Repeated programs.
			Preterm::ExpLet { grade, grade_argument, argument, tail } => self.elaborate_static_exp_let(
				PreExpLet { grade: grade.unwrap_or(1.into()), grade_argument, argument: *argument, tail },
				(),
				|ctx, tail, ()| ctx.synthesize_static(tail),
				|grade, grade_argument, argument, tail| {
					let (tail, tail_ty, c) = tail.retract2();
					(
						StaticTerm::ExpLet {
							grade,
							grade_argument,
							argument: argument.into(),
							tail: tail.map_into(),
						},
						tail_ty,
						c,
					)
				},
			)?,

			// Dependent functions.
			Preterm::Pi { grade, base, family } if self.fragment == Fragment::Logical => {
				let (base, base_copy) = self.elaborate_static_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_copy) = self
					.extend(family)
					.bind_static(false, 0.into(), base_copy, base_value)
					.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
				(
					StaticTerm::Pi { grade, base_copy, base: base.into(), family_copy, family: family.map_into() },
					StaticValue::Universe(family_copy),
					Cpy::Tr,
				)
			}
			Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
			Preterm::Call { callee, argument } => {
				let (callee, scrutinee_ty, _) = self.synthesize_static(*callee)?;
				let StaticValue::IndexedProduct { grade, base, family_copy, family, .. } = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let argument =
					self.amplify(grade).erase_if(grade == 0).verify_static(*argument, (*base).clone())?;
				(
					StaticTerm::Apply { scrutinee: callee.into(), argument: argument.clone().into() },
					family.evaluate_with([argument.evaluate_in(&self.environment)]),
					family_copy,
				)
			}

			// Dependent pairs.
			Preterm::Sg { base, family } => {
				let (base, base_copy) = self.elaborate_static_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_copy) = self
					.extend(family)
					.bind_static(false, 0.into(), base_copy, base_value)
					.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
				(
					StaticTerm::Sg { base_copy, base: base.into(), family_copy, family: family.map_into() },
					StaticValue::Universe(base_copy.max(family_copy)),
					Cpy::Tr,
				)
			}
			Preterm::Pair { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
			Preterm::SgLet { grade, argument, tail } => self.elaborate_static_sg_let(
				PreSgLet { grade, argument: *argument, tail },
				(),
				|ctx, tail_body, ()| ctx.synthesize_static(tail_body),
				|grade, argument, tail| {
					let (tail, tail_ty, c) = tail.retract2();
					(StaticTerm::SgLet { grade, argument: argument.into(), tail: tail.map_into() }, tail_ty, c)
				},
			)?,

			// Generic type formers.
			Preterm::Former(former, arguments) if self.fragment == Fragment::Logical => match former {
				// Types and universe indices.
				Former::Universe => {
					let [c] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					match c.preterm {
						ParsedPreterm(Preterm::Constructor(Constructor::Cpy(c), v)) if v.is_empty() =>
							(StaticTerm::Universe(c), StaticValue::Universe(Cpy::Tr), Cpy::Tr),
						_ => return Err(ElaborationErrorKind::InvalidStaticUniverse.at(expr.range)),
					}
				}
				Former::Copy if arguments.is_empty() =>
					(StaticTerm::Cpy, StaticValue::Universe(Cpy::Tr), Cpy::Tr),
				Former::Repr if arguments.is_empty() =>
					(StaticTerm::Repr, StaticValue::Universe(Cpy::Tr), Cpy::Tr),

				// Quoting.
				Former::Lift => {
					let [liftee] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (liftee, kind) = self.elaborate_dynamic_type(liftee)?;
					(
						StaticTerm::Lift { liftee: liftee.into(), kind: kind.unevaluate_in(self.len()).into() },
						StaticValue::Universe(Cpy::Nt),
						Cpy::Tr,
					)
				}

				// Repeated programs.
				Former::Exp(grade) => {
					let [ty] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (ty, c) = self.elaborate_static_type(ty)?;
					(
						StaticTerm::Exp(grade, c, ty.into()),
						StaticValue::Universe(if grade == 0.into() { Cpy::Tr } else { c }),
						Cpy::Tr,
					)
				}

				// Enumerated numbers.
				Former::Enum(card) if arguments.is_empty() =>
					(StaticTerm::Enum(card), StaticValue::Universe(Cpy::Tr), Cpy::Tr),

				// Natural numbers.
				Former::Nat if arguments.is_empty() => (StaticTerm::Nat, StaticValue::Universe(Cpy::Tr), Cpy::Tr),

				// Invalid former.
				_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
			},

			// Generic term constructors.
			Preterm::Constructor(constructor, arguments) => match constructor {
				// Universe indices.
				Constructor::Cpy(c) if self.fragment == Fragment::Logical && arguments.is_empty() => (
					match c {
						Cpy::Tr => StaticTerm::CpyMax(vec![]),
						Cpy::Nt => StaticTerm::CpyNt,
					},
					StaticValue::Cpy,
					Cpy::Tr,
				),
				Constructor::CpyMax if self.fragment == Fragment::Logical => (
					StaticTerm::CpyMax(
						arguments
							.into_iter()
							.map(|a| self.verify_static(a, StaticValue::Cpy))
							.collect::<Result<_, _>>()?,
					),
					StaticValue::Cpy,
					Cpy::Tr,
				),
				Constructor::ReprAtom(r) if self.fragment == Fragment::Logical && arguments.is_empty() =>
					(StaticTerm::ReprAtom(r), StaticValue::ReprType, Cpy::Tr),
				Constructor::ReprExp(n) if self.fragment == Fragment::Logical => {
					let [r] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let r = self.verify_static(r, StaticValue::ReprType)?;
					(StaticTerm::ReprExp(n, r.into()), StaticValue::ReprType, Cpy::Tr)
				}
				Constructor::ReprPair if self.fragment == Fragment::Logical => {
					let [r0, r1] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let r0 = self.verify_static(r0, StaticValue::ReprType)?;
					let r1 = self.verify_static(r1, StaticValue::ReprType)?;
					(StaticTerm::ReprPair(r0.into(), r1.into()), StaticValue::ReprType, Cpy::Tr)
				}

				// Repeated programs.
				Constructor::Exp(grade) => {
					let [tm] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (tm, ty, c) = self.synthesize_static(tm)?;
					(
						StaticTerm::Repeat(grade, tm.into()),
						StaticValue::Exp(grade, c, ty.into()),
						if grade == 0.into() { Cpy::Tr } else { c },
					)
				}

				// Enumerated numbers.
				Constructor::Enum(k, v) if arguments.is_empty() =>
					(StaticTerm::EnumValue(k, v), StaticValue::Enum(k), Cpy::Tr),

				// Natural numbers.
				Constructor::Num(n) if arguments.is_empty() => (StaticTerm::Num(n), StaticValue::Nat, Cpy::Tr),
				Constructor::Suc => {
					let [prev] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let prev = self.verify_static(prev, StaticValue::Nat)?;
					if let StaticTerm::Num(p) = prev {
						(StaticTerm::Num(p + 1), StaticValue::Nat, Cpy::Tr)
					} else {
						(StaticTerm::Suc(prev.into()), StaticValue::Nat, Cpy::Tr)
					}
				}

				// Invalid constructor.
				_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
			},

			// Generic projectors.
			Preterm::Project(scrutinee, projector) => match projector {
				// Repeated programs.
				Projector::Exp if self.fragment == Fragment::Logical => {
					let (scrutinee, scrutinee_ty, _) = self.synthesize_static(*scrutinee)?;
					let StaticValue::Exp(_, c, ty) = scrutinee_ty else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(expr.range));
					};
					(StaticTerm::ExpProject(scrutinee.into()), ty.as_ref().clone(), c)
				}

				// Dependent pairs.
				Projector::Field(field) if self.fragment == Fragment::Logical => {
					let (scrutinee, scrutinee_ty, _) = self.synthesize_static(*scrutinee)?;
					let StaticValue::IndexedSum { base_copy, base, family_copy, family, .. } = scrutinee_ty else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
					};
					match field {
						Field::Base =>
							(StaticTerm::SgField(scrutinee.into(), field), base.as_ref().clone(), base_copy),
						Field::Fiber => (
							StaticTerm::SgField(scrutinee.clone().into(), field),
							family.evaluate_with([StaticTerm::SgField(scrutinee.clone().into(), Field::Base)
								.evaluate_in(&self.environment)]),
							family_copy,
						),
					}
				}

				// Invalid projector.
				_ => return Err(ElaborationErrorKind::InvalidProjector.at(expr.range)),
			},

			// Generic case splits.
			Preterm::Split { scrutinee, is_cast: false, motive, cases } => {
				let (scrutinee, scrutinee_ty, _) = self.synthesize_static(*scrutinee)?;
				let scrutinee_value = scrutinee.clone().evaluate_in(&self.environment);
				match scrutinee_ty {
					StaticValue::Enum(card) => {
						let motive = motive
							.try_resolve::<1>()
							.map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;
						(cases.len() == card as _)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						let (motive_term, motive_copy) = self
							.extend(motive)
							.bind_static(false, 0.into(), Cpy::Tr, StaticValue::Enum(card))
							.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
						let motive_value = motive_term.clone().map_into().evaluate_in(&self.environment);
						// TODO: Avoid cloning.
						let mut new_cases = Vec::new();
						for v in 0..card {
							let v = v as u8;
							let Some(case_position) = cases.iter().position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::Enum(target_card, target_v), args) = pattern
								{
									*target_card == card && *target_v == v && args.is_empty()
								} else {
									false
								}
							}) else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							let case = cases[case_position].1.clone();
							new_cases.push(
								self.amplify(Cost::Inf).verify_static(
									case,
									motive_value.evaluate_with([StaticValue::EnumValue(card, v)]),
								)?,
							)
						}

						(
							StaticTerm::CaseEnum {
								scrutinee: scrutinee.into(),
								motive: motive_term.map_into(),
								cases: new_cases,
							},
							motive_value.evaluate_with([scrutinee_value]),
							motive_copy,
						)
					}

					// Natural numbers.
					StaticValue::Nat => {
						let motive = motive
							.try_resolve::<1>()
							.map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;
						(cases.len() == 2)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						let (motive, motive_c) = self
							.extend(motive)
							.bind_static(false, 0.into(), Cpy::Tr, StaticValue::Nat)
							.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
						let motive_value = motive.clone().map_into().evaluate_in(&self.environment);
						// Avoid cloning.
						let Some(case_nil_position) = cases.iter().position(|(pattern, _)| {
							if let Pattern::Construction(Constructor::Num(0), args) = pattern {
								args.is_empty()
							} else {
								false
							}
						}) else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let case_nil = cases[case_nil_position].1.clone();
						let case_suc_parameters = {
							let Pattern::Construction(Constructor::Suc, args) =
								cases[1 - case_nil_position].0.clone()
							else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							let [arg] = args
								.try_into()
								.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
							let Pattern::Witness { index, witness } = arg else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							[index, witness]
						};
						let case_suc = bind(case_suc_parameters, cases[1 - case_nil_position].1.clone());
						let case_nil =
							self.verify_static(case_nil, motive_value.evaluate_with([StaticValue::Num(0)]))?;
						let case_suc = self
							.amplify(Cost::Inf)
							.extend(case_suc)
							.bind_static(false, Cost::Inf, Cpy::Tr, StaticValue::Nat)
							.bind_static_with(false, 1.into(), motive_c, |ctx| {
								motive_value.evaluate_with([ctx.var(0)])
							})
							.map(|ctx, body| {
								ctx.verify_static(body, motive_value.evaluate_with([ctx.var::<StaticValue>(1).suc()]))
							})?;
						(
							StaticTerm::CaseNat {
								scrutinee: scrutinee.into(),
								motive: motive.map_into(),
								case_nil: case_nil.into(),
								case_suc: case_suc.map_into(),
							},
							motive_value.evaluate_with([scrutinee_value]),
							motive_c,
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

	fn verify_static(&mut self, expr: Expression, ty: StaticValue) -> Result<StaticTerm, ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match (preterm, ty) {
			// Let-expressions.
			(Preterm::Let { is_meta: true, grade, ty, argument, tail }, tail_ty) => self.elaborate_static_let(
				PreLet { grade, ty: *ty, argument: *argument, tail },
				tail_ty,
				Self::verify_static,
				|grade, ty, argument, tail| StaticTerm::Let {
					grade,
					ty: ty.into(),
					argument: argument.into(),
					tail: tail.map_into(),
				},
			)?,

			// Quoted programs.
			(Preterm::SwitchLevel(quotee), ty) => {
				let StaticValue::Lift { ty: liftee, .. } = ty else {
					return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
				};
				let quotee = self.verify_dynamic(*quotee, liftee)?;
				StaticTerm::Quote(quotee.into())
			}

			// Repeated programs.
			(Preterm::ExpLet { grade, grade_argument, argument, tail }, tail_ty) => self
				.elaborate_static_exp_let(
					PreExpLet { grade: grade.unwrap_or(1.into()), grade_argument, argument: *argument, tail },
					tail_ty,
					Self::verify_static,
					|grade, grade_argument, argument, tail| StaticTerm::ExpLet {
						grade,
						grade_argument,
						argument: argument.into(),
						tail: tail.map_into(),
					},
				)?,

			// Dependent functions.
			(
				Preterm::Lambda { grade, body },
				StaticValue::IndexedProduct { grade: grade_v, base_copy, base, family_copy: _, family },
			) => {
				(self.fragment == Fragment::Logical || grade == grade_v)
					.then_some(())
					.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_v).at(expr.range))?;
				let body = self
					.extend(body)
					.bind_static(false, grade.into(), base_copy, base.as_ref().clone())
					.map(|ctx, body| ctx.verify_static(*body, family.evaluate_with([ctx.var(0)])))?;
				StaticTerm::Function(grade, body.map_into())
			}

			// Dependent pairs.
			(
				Preterm::Pair { basepoint, fiberpoint },
				StaticValue::IndexedSum { base_copy: _, base, family_copy: _, family },
			) => {
				let basepoint = self.verify_static(*basepoint, base.as_ref().clone())?;
				let basepoint_value = basepoint.clone().evaluate_in(&self.environment);
				let fiberpoint = self.verify_static(*fiberpoint, family.evaluate_with([basepoint_value]))?;
				StaticTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
			}
			(Preterm::SgLet { grade, argument, tail }, tail_ty) => self.elaborate_static_sg_let(
				PreSgLet { grade, argument: *argument, tail },
				tail_ty,
				Self::verify_static,
				|grade, argument, tail| StaticTerm::SgLet {
					grade,
					argument: argument.into(),
					tail: tail.map_into(),
				},
			)?,

			// Synthesize and conversion-check.
			(term, ty) => {
				let (term, synthesized_ty, _) = self.synthesize_static(term.at(expr.range))?;
				if self.len().can_convert(&synthesized_ty, &ty) {
					term
				} else {
					return Err(
						ElaborationErrorKind::StaticBidirectionalMismatch {
							synthesized: synthesized_ty.unevaluate_in(self.len()),
							expected: ty.unevaluate_in(self.len()),
						}
						.at(expr.range),
					);
				}
			}
		})
	}

	fn synthesize_dynamic(
		&mut self,
		expr: Expression,
	) -> Result<(DynamicTerm, DynamicValue, KindValue), ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match preterm {
			// Variables.
			Preterm::Variable(name) => 'var: {
				for (i, (name_1, entry)) in self.tys.iter().rev().enumerate() {
					if &Some(name) == name_1 {
						if let ContextType::Dynamic(ty, kind) = &entry.ty {
							let result = (DynamicTerm::Variable(Some(name), Index(i)), ty.clone(), kind.clone());
							self.take_index(i).map_err(|e| e.at(expr.range))?;
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
					self.elaborate_static_let(
						PreLet { grade, ty: *ty, argument: *argument, tail },
						(),
						|ctx, tail_body, ()| ctx.synthesize_dynamic(tail_body),
						|grade, ty, argument, tail| {
							let (tail, tail_ty, tail_kind) = tail.retract2();
							(
								DynamicTerm::Def {
									grade,
									ty: ty.into(),
									argument: argument.into(),
									tail: tail.map_into(),
								},
								tail_ty,
								tail_kind,
							)
						},
					)?
				} else {
					self.elaborate_dynamic_let(
						PreLet { grade, ty: *ty, argument: *argument, tail },
						(),
						|ctx, tail_body, ()| ctx.synthesize_dynamic(tail_body),
						|grade, ty, argument_kind, argument, tail| {
							let (tail, tail_ty, tail_kind) = tail.retract2();
							(
								DynamicTerm::Let {
									grade,
									ty: ty.into(),
									argument_kind: argument_kind.into(),
									argument: argument.into(),
									tail: tail.map_into(),
								},
								tail_ty,
								tail_kind,
							)
						},
					)?
				},

			// Splicing.
			Preterm::SwitchLevel(splicee) => {
				let (splicee, StaticValue::Lift { ty: liftee, kind }, _) = self.synthesize_static(*splicee)?
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
				};
				(DynamicTerm::Splice(splicee.into()), liftee, (*kind).clone())
			}

			// Repeated programs.
			Preterm::ExpLet { grade, grade_argument, argument, tail } => self.elaborate_dynamic_exp_let(
				PreExpLet { grade: grade.unwrap_or(1.into()), grade_argument, argument: *argument, tail },
				(),
				|ctx, tail_body, ()| ctx.synthesize_dynamic(tail_body),
				|grade, grade_argument, argument, kind_arg, tail| {
					let (tail, tail_ty, kind) = tail.retract2();
					(
						DynamicTerm::ExpLet {
							grade,
							grade_argument,
							argument: argument.into(),
							kind: kind_arg.into(),
							tail: tail.map_into(),
						},
						tail_ty,
						kind,
					)
				},
			)?,

			// Dependent functions.
			Preterm::Pi { grade, base, family } if self.fragment == Fragment::Logical => {
				let (base, base_kind) = self.elaborate_dynamic_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_kind) = self
					.extend(family)
					.bind_dynamic(false, 0.into(), base_kind.clone(), base_value)
					.map(|ctx, body| ctx.elaborate_dynamic_type(*body))?
					.retract();
				let Ok(family_kind) = family_kind.try_unevaluate_in(self.len()) else {
					return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
				};
				(
					DynamicTerm::Pi {
						grade,
						base_kind: base_kind.unevaluate_in(self.len()).into(),
						base: base.into(),
						family_kind: family_kind.into(),
						family: family.map_into(),
					},
					DynamicValue::Universe { kind: KindValue::fun().into() },
					KindValue::ty(),
				)
			}
			Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
			Preterm::Call { callee, argument } => {
				let (scrutinee, scrutinee_ty, _) = self.synthesize_dynamic(*callee)?;
				let DynamicValue::IndexedProduct { grade, base, family_kind, family, .. } = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let argument =
					self.amplify(grade).erase_if(grade == 0).verify_dynamic(*argument, (*base).clone())?;
				let argument_value = argument.clone().evaluate_in(&self.environment);
				(
					DynamicTerm::Apply {
						scrutinee: scrutinee.into(),
						grade: Some(grade),
						argument: argument.into(),
						family_kind: Some(family_kind.unevaluate_in(self.len()).into()),
					},
					family.evaluate_with([argument_value]),
					(*family_kind).clone(),
				)
			}

			// Dependent pairs.
			Preterm::Sg { base, family } if self.fragment == Fragment::Logical => {
				let (base, base_kind) = self.elaborate_dynamic_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_kind) = self
					.extend(family)
					.bind_dynamic(false, 0.into(), base_kind.clone(), base_value)
					.map_extra(|ctx, body| ctx.elaborate_dynamic_type(*body))?;
				let kind = KindValue::pair(self.len(), base_kind.clone(), family_kind.clone());
				let Ok(family_kind) = family_kind.try_unevaluate_in(self.len()) else {
					return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
				};
				(
					DynamicTerm::Sg {
						base_kind: base_kind.unevaluate_in(self.len()).into(),
						base: base.into(),
						family_kind: family_kind.into(),
						family: family.map_into(),
					},
					DynamicValue::Universe { kind: kind.into() },
					KindValue::ty(),
				)
			}
			Preterm::Pair { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
			Preterm::SgLet { grade, argument, tail } => self.elaborate_dynamic_sg_let(
				PreSgLet { grade, argument: *argument, tail },
				(),
				|ctx, tail_body, ()| ctx.synthesize_dynamic(tail_body),
				|grade, kinds, argument, tail| {
					let (tail, tail_ty, kind) = tail.retract2();
					(
						DynamicTerm::SgLet { grade, kinds, argument: argument.into(), tail: tail.map_into() },
						tail_ty,
						kind,
					)
				},
			)?,

			// Generic type formers.
			Preterm::Former(former, arguments) if self.fragment == Fragment::Logical => match former {
				// Types.
				Former::Universe => {
					let [copy, repr] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let copy = self.verify_static(copy, StaticValue::Cpy)?;
					let repr = self.verify_static(repr, StaticValue::ReprType)?;
					(
						DynamicTerm::Universe { kind: KindTerm { copy, repr }.into() },
						DynamicValue::Universe { kind: KindValue::ty().into() },
						KindValue::ty(),
					)
				}

				// Repeated programs.
				Former::Exp(Cost::Fin(grade)) => {
					let [ty] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (ty, kind) = self.elaborate_dynamic_type(ty)?;
					(
						DynamicTerm::Exp(grade, kind.unevaluate_in(self.len()).into(), ty.into()),
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
					let [ty, x, y] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (ty, kind) = self.elaborate_dynamic_type(ty)?;
					let ty_value = ty.clone().evaluate_in(&self.environment);
					let x = self.verify_dynamic(x, ty_value.clone())?;
					let y = self.verify_dynamic(y, ty_value.clone())?;
					(
						DynamicTerm::Id {
							kind: kind.unevaluate_in(self.len()).into(),
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
					let [ty] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (ty, kind) = self.elaborate_dynamic_type(ty)?;
					(
						DynamicTerm::Bx { kind: kind.unevaluate_in(self.len()).into(), inner: ty.into() },
						DynamicValue::Universe { kind: KindValue::ptr().into() },
						KindValue::ty(),
					)
				}
				Former::Wrap => {
					let [ty] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (ty, kind) = self.elaborate_dynamic_type(ty)?;
					(
						DynamicTerm::Wrap { inner: ty.into(), kind: kind.unevaluate_in(self.len()).into() },
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
					let [tm] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (tm, ty, kind) = self.synthesize_dynamic(tm)?;
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
					let [prev] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let prev = self.verify_dynamic(prev, DynamicValue::Nat)?;
					if let DynamicTerm::Num(p) = prev {
						(DynamicTerm::Num(p + 1), DynamicValue::Nat, KindValue::nat())
					} else {
						(DynamicTerm::Suc(prev.into()), DynamicValue::Nat, KindValue::nat())
					}
				}

				// Wrappers.
				Constructor::Bx => {
					let [tm] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (tm, ty, kind) = self.synthesize_dynamic(tm)?;
					(
						DynamicTerm::BxValue(tm.into()),
						DynamicValue::Bx { inner: ty.into(), kind: kind.into() },
						KindValue::ptr(),
					)
				}
				Constructor::Wrap => {
					let [tm] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let (tm, ty, kind) = self.synthesize_dynamic(tm)?;
					(
						DynamicTerm::WrapValue(tm.into()),
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
				Projector::Exp if self.fragment == Fragment::Logical => {
					let (scrutinee, scrutinee_ty, _) = self.synthesize_dynamic(*scrutinee)?;
					let DynamicValue::Exp(_, kind, ty) = scrutinee_ty else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(expr.range));
					};
					(DynamicTerm::ExpProject(scrutinee.into()), ty.as_ref().clone(), (*kind).clone())
				}

				// Dependent pairs.
				Projector::Field(field) if self.fragment == Fragment::Logical => {
					let (scrutinee, scrutinee_ty, _) = self.synthesize_dynamic(*scrutinee)?;
					let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = scrutinee_ty else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
					};
					let basepoint =
						DynamicTerm::SgField { scrutinee: scrutinee.clone().into(), field: Field::Base };
					match field {
						Field::Base => (basepoint, base.as_ref().clone(), (*base_kind).clone()),
						Field::Fiber => (
							DynamicTerm::SgField { scrutinee: scrutinee.into(), field },
							family.evaluate_with([basepoint.evaluate_in(&self.environment)]),
							(*family_kind).clone(),
						),
					}
				}

				// Wrappers.
				Projector::Bx => {
					let (tm, DynamicValue::Bx { inner: ty, kind }, _) = self.synthesize_dynamic(*scrutinee)?
					else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Bx).at(expr.range));
					};
					(
						DynamicTerm::BxProject {
							scrutinee: tm.into(),
							kind: Some(kind.unevaluate_in(self.len()).into()),
						},
						ty.as_ref().clone(),
						(*kind).clone(),
					)
				}

				Projector::Wrap => {
					let (tm, DynamicValue::Wrap { inner: ty, kind }, _) = self.synthesize_dynamic(*scrutinee)?
					else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Wrap).at(expr.range));
					};
					(
						DynamicTerm::WrapProject {
							scrutinee: tm.into(),
							kind: Some(kind.unevaluate_in(self.len()).into()),
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
				let (scrutinee, scrutinee_ty, _) = if is_cast {
					self.erase().synthesize_dynamic(*scrutinee)
				} else {
					self.synthesize_dynamic(*scrutinee)
				}?;
				let scrutinee_value = scrutinee.clone().evaluate_in(&self.environment);
				match scrutinee_ty {
					DynamicValue::Id { kind, space, left, right }
						if is_cast || self.fragment == Fragment::Logical =>
					{
						let motive = motive
							.try_resolve::<2>()
							.map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;
						let Ok([(Pattern::Construction(Constructor::Refl, patterns), case_refl)]) =
							<[_; 1]>::try_from(cases)
						else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let [] =
							patterns.try_into().map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;

						let (motive_term, motive_kind) = self
							.extend(motive)
							.bind_dynamic(false, 0.into(), (*kind).clone(), (*space).clone())
							.bind_dynamic_with(false, 0.into(), KindValue::path(), |ctx| DynamicValue::Id {
								kind,
								space: space.clone(),
								left: left.clone(),
								right: Rc::new(ctx.var(0)),
							})
							.map_extra(|ctx, body| ctx.elaborate_dynamic_type(*body))?;
						let Ok(_) = motive_kind.try_unevaluate_in(self.len()) else {
							return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
						};
						let motive = motive_term.clone().map_into().evaluate_in(&self.environment);

						let case_refl = self.verify_dynamic(
							case_refl,
							motive.evaluate_with([(*left).clone(), DynamicValue::Refl]),
						)?;

						(
							DynamicTerm::CasePath {
								scrutinee: scrutinee.into(),
								motive: motive_term.map_into(),
								case_refl: case_refl.into(),
							},
							motive.evaluate_with([(*right).clone(), scrutinee_value]),
							motive_kind,
						)
					}

					// Enumerated numbers.
					DynamicValue::Enum(card) if !is_cast => {
						let motive = motive
							.try_resolve::<1>()
							.map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;
						(cases.len() == card as _)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						let (motive_term, motive_kind) = self
							.extend(motive)
							.bind_dynamic(false, 0.into(), KindValue::enu(), DynamicValue::Enum(card))
							.map_extra(|ctx, body| ctx.elaborate_dynamic_type(*body))?;
						let Ok(_) = motive_kind.try_unevaluate_in(self.len()) else {
							return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
						};
						let motive = motive_term.clone().map_into().evaluate_in(&self.environment);
						// TODO: Avoid cloning.
						let mut new_cases = Vec::new();
						for v in 0..card {
							let v = v as u8;
							let Some(case_position) = cases.iter().position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::Enum(target_card, target_v), patterns) =
									pattern
								{
									*target_card == card && *target_v == v && patterns.is_empty()
								} else {
									false
								}
							}) else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							let case = cases[case_position].1.clone();
							new_cases.push(
								self
									.amplify(Cost::Inf)
									.verify_dynamic(case, motive.evaluate_with([DynamicValue::EnumValue(card, v)]))?,
							)
						}
						(
							DynamicTerm::CaseEnum {
								scrutinee: scrutinee.into(),
								cases: new_cases,
								motive: motive_term.map_into(),
								motive_kind: Some(motive_kind.unevaluate_in(self.len()).into()),
							},
							motive.evaluate_with([scrutinee_value]),
							motive_kind,
						)
					}

					// Natural numbers.
					DynamicValue::Nat if !is_cast => {
						let motive = motive
							.try_resolve::<1>()
							.map_err(|_| ElaborationErrorKind::WrongArity.at(expr.range))?;
						(cases.len() == 2)
							.then_some(())
							.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
						let (motive_term, motive_kind) = self
							.extend(motive)
							.bind_dynamic(false, 0.into(), KindValue::nat(), DynamicValue::Nat)
							.map_extra(|ctx, body| ctx.elaborate_dynamic_type(*body))?;
						let Ok(_) = motive_kind.try_unevaluate_in(self.len()) else {
							return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
						};
						let motive_value = motive_term.clone().map_into().evaluate_in(&self.environment);
						// Avoid cloning.
						let Some(case_nil_position) = cases.iter().position(|(pattern, _)| {
							if let Pattern::Construction(Constructor::Num(0), args) = pattern {
								args.is_empty()
							} else {
								false
							}
						}) else {
							return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
						};
						let case_nil = cases[case_nil_position].1.clone();
						let case_suc_parameters = {
							let Pattern::Construction(Constructor::Suc, args) =
								cases[1 - case_nil_position].0.clone()
							else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							let [arg] = args
								.try_into()
								.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
							let Pattern::Witness { index, witness } = arg else {
								return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
							};
							[index, witness]
						};
						let case_suc = cases[1 - case_nil_position].1.clone();
						let case_nil =
							self.verify_dynamic(case_nil, motive_value.evaluate_with([DynamicValue::Num(0)]))?;
						let case_suc = self
							.amplify(Cost::Inf)
							.extend(bind(case_suc_parameters, case_suc))
							// NOTE: Unrestricted usage is only "safe" because we're approximating Nat with a finite type.
							// For nontrivial Nat, we may wish to enclose the index with a thunk.
							.bind_dynamic(false, Cost::Inf, KindValue::nat(), DynamicValue::Nat)
							.bind_dynamic_with(false, 1.into(), motive_kind.clone(), |ctx| {
								motive_value.evaluate_with([ctx.var(0)])
							})
							.map(|ctx, body| {
								ctx.verify_dynamic(
									body,
									motive_value.evaluate_with([ctx.var::<DynamicValue>(1).suc()]),
								)
							})?;
						(
							DynamicTerm::CaseNat {
								scrutinee: scrutinee.into(),
								motive_kind: Some(motive_kind.unevaluate_in(self.len()).into()),
								motive: motive_term.map_into(),
								case_nil: case_nil.into(),
								case_suc: case_suc.map_into(),
							},
							motive_value.evaluate_with([scrutinee_value]),
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

	fn verify_dynamic(&mut self, expr: Expression, ty: DynamicValue) -> Result<DynamicTerm, ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match (preterm, ty) {
			// Let-expressions.
			(Preterm::Let { is_meta, grade, ty, argument, tail }, tail_ty) =>
				if is_meta {
					self.elaborate_static_let(
						PreLet { grade, ty: *ty, argument: *argument, tail },
						tail_ty,
						Self::verify_dynamic,
						|grade, ty, argument, tail| DynamicTerm::Def {
							grade,
							ty: ty.into(),
							argument: argument.into(),
							tail: tail.map_into(),
						},
					)?
				} else {
					self.elaborate_dynamic_let(
						PreLet { grade, ty: *ty, argument: *argument, tail },
						tail_ty,
						Self::verify_dynamic,
						|grade, ty, argument_kind, argument, tail| DynamicTerm::Let {
							grade,
							ty: ty.into(),
							argument_kind: argument_kind.into(),
							argument: argument.into(),
							tail: tail.map_into(),
						},
					)?
				},

			// Repeated programs.
			(Preterm::ExpLet { grade, grade_argument, argument, tail }, tail_ty) => self
				.elaborate_dynamic_exp_let(
					PreExpLet { grade: grade.unwrap_or(1.into()), grade_argument, argument: *argument, tail },
					tail_ty,
					Self::verify_dynamic,
					|grade, grade_argument, argument, kind_arg, tail| DynamicTerm::ExpLet {
						grade,
						grade_argument,
						argument: argument.into(),
						kind: kind_arg.into(),
						tail: tail.map_into(),
					},
				)?,

			// Dependent functions.
			(
				Preterm::Lambda { grade, body },
				DynamicValue::IndexedProduct { grade: grade_t, base_kind, base, family_kind, family },
			) => {
				(self.fragment == Fragment::Logical || grade == grade_t)
					.then_some(())
					.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_t).at(expr.range))?;
				let body = self
					.extend(body)
					.bind_dynamic(false, grade.into(), (*base_kind).clone(), base.as_ref().clone())
					.map(|ctx, body| ctx.verify_dynamic(*body, family.evaluate_with([ctx.var(0)])))?;
				DynamicTerm::Function {
					grade,
					body: body.map_into(),
					domain_kind: Some(base_kind.unevaluate_in(self.len()).into()),
					codomain_kind: Some(family_kind.unevaluate_in(self.len()).into()),
				}
			}

			// Dependent pairs.
			(Preterm::Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
				let basepoint = self.verify_dynamic(*basepoint, base.as_ref().clone())?;
				let basepoint_value = basepoint.clone().evaluate_in(&self.environment);
				let fiberpoint = self.verify_dynamic(*fiberpoint, family.evaluate_with([basepoint_value]))?;
				DynamicTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }
			}
			(Preterm::SgLet { grade, argument, tail }, tail_ty) => self.elaborate_dynamic_sg_let(
				PreSgLet { grade, argument: *argument, tail },
				tail_ty,
				Self::verify_dynamic,
				|grade, kinds, argument, tail| DynamicTerm::SgLet {
					grade,
					kinds,
					argument: argument.into(),
					tail: tail.map_into(),
				},
			)?,

			// Paths.
			(Preterm::Constructor(Constructor::Refl, tms), ty) if self.fragment == Fragment::Logical => {
				let DynamicValue::Id { left, right, .. } = ty else {
					return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Id).at(expr.range));
				};
				assert!(self.len().can_convert(&*left, &right));

				let [] = tms.try_into().map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
				DynamicTerm::Refl
			}

			// Wrappers.
			(Preterm::Constructor(Constructor::Bx, tms), ty) => {
				let DynamicValue::Bx { inner: ty, .. } = ty else {
					return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Bx).at(expr.range));
				};
				let [tm] =
					tms.try_into().map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
				let tm = self.verify_dynamic(tm, ty.as_ref().clone())?;
				DynamicTerm::BxValue(tm.into())
			}
			(Preterm::Constructor(Constructor::Wrap, tms), ty) => {
				let DynamicValue::Wrap { inner: ty, .. } = ty else {
					return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Wrap).at(expr.range));
				};
				let [tm] =
					tms.try_into().map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
				let tm = self.verify_dynamic(tm, ty.as_ref().clone())?;
				DynamicTerm::WrapValue(tm.into())
			}

			// Synthesize and conversion-check.
			(term, ty) => {
				let (term, synthesized_ty, _) = self.synthesize_dynamic(term.at(expr.range))?;
				if self.len().can_convert(&synthesized_ty, &ty) {
					term
				} else {
					return Err(
						ElaborationErrorKind::DynamicBidirectionalMismatch {
							synthesized: synthesized_ty.unevaluate_in(self.len()),
							expected: ty.unevaluate_in(self.len()),
						}
						.at(expr.range),
					);
				}
			}
		})
	}

	fn elaborate_static_type(&mut self, expr: Expression) -> Result<(StaticTerm, Cpy), ElaborationError> {
		let expr_range = expr.range;
		let (term, StaticValue::Universe(c), _) = self.erase().synthesize_static(expr)? else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
		};
		Ok((term, c))
	}

	fn elaborate_dynamic_type(
		&mut self,
		expr: Expression,
	) -> Result<(DynamicTerm, KindValue), ElaborationError> {
		let expr_range = expr.range;
		let (term, DynamicValue::Universe { kind }, _) = self.erase().synthesize_dynamic(expr)? else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
		};
		Ok((term, (*kind).clone()))
	}

	fn elaborate_static_let<A, B>(
		&mut self,
		PreLet { grade, ty, argument, tail }: PreLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(Cost, StaticTerm, StaticTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let grade = grade.unwrap_or_else(|| if tail.parameter().label.is_some() { 1 } else { 0 }.into());
		let (ty, ty_c) = self.elaborate_static_type(ty)?;
		let ty_value = ty.clone().evaluate_in(&self.environment);
		let argument =
			self.amplify(grade).erase_if(grade == 0.into()).verify_static(argument, ty_value.clone())?;
		// TODO: Lazy evaluation.
		let argument_value = argument.clone().evaluate_in(&self.environment);
		let tail_b = self
			.extend(tail)
			.alias_static(false, grade, ty_c, ty_value, argument_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;
		Ok(produce_let(grade, ty, argument, tail_b))
	}

	fn elaborate_dynamic_let<A, B>(
		&mut self,
		PreLet { grade, ty, argument, tail }: PreLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(usize, DynamicTerm, KindTerm, DynamicTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let grade = grade.unwrap_or_else(|| if tail.parameter().label.is_some() { 1 } else { 0 }.into());
		let Cost::Fin(grade) = grade else {
			return Err(
				ElaborationErrorKind::InvalidGrade.at((tail.parameter().locus, tail.parameter().locus + 1)),
			);
		};
		let (ty, argument_kind) = self.elaborate_dynamic_type(ty)?;
		let ty_value = ty.clone().evaluate_in(&self.environment);
		let argument = self.amplify(grade).erase_if(grade == 0).verify_dynamic(argument, ty_value.clone())?;
		// TODO: Lazy evaluation.
		let argument_value = argument.clone().evaluate_in(&self.environment);
		let tail_b = self
			.extend(tail)
			.alias_dynamic(false, grade.into(), argument_kind.clone(), ty_value, argument_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		let argument_kind = argument_kind.unevaluate_in(self.len());

		Ok(produce_let(grade, ty, argument_kind, argument, tail_b))
	}

	fn elaborate_static_exp_let<A, B>(
		&mut self,
		PreExpLet { grade, grade_argument, argument, tail }: PreExpLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(Cost, Cost, StaticTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let argument_range = argument.range;
		let (tm, ty, _) = self.amplify(grade).erase_if(grade == 0.into()).synthesize_static(argument)?;
		let StaticValue::Exp(n, c, ty) = ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		};
		if n != grade_argument {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		}
		let rep_value = tm.clone().evaluate_in(&self.environment);
		let inner_value = rep_value.clone().exp_project();
		let tail_b = self
			.extend(tail)
			.alias_static(false, grade * grade_argument, c, (*ty).clone(), inner_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, grade_argument, tm, tail_b))
	}

	fn elaborate_dynamic_exp_let<A, B>(
		&mut self,
		PreExpLet { grade, grade_argument, argument, tail }: PreExpLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(usize, usize, DynamicTerm, KindTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let (Cost::Fin(grade), Cost::Fin(grade_argument)) = (grade, grade_argument) else {
			return Err(ElaborationErrorKind::InvalidGrade.at(argument.range));
		};
		let argument_range = argument.range;
		let (tm, ty, _) = self.amplify(grade).erase_if(grade == 0).synthesize_dynamic(argument)?;
		let DynamicValue::Exp(n, kind, ty) = ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		};
		if n != grade_argument {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		}
		let rep_value = tm.clone().evaluate_in(&self.environment);
		let inner_value = rep_value.clone().exp_project();
		let tail_b = self
			.extend(tail)
			.alias_dynamic(false, (grade * grade_argument).into(), (*kind).clone(), (*ty).clone(), inner_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, grade_argument, tm, kind.unevaluate_in(self.len()), tail_b))
	}

	fn elaborate_static_sg_let<A, B>(
		&mut self,
		PreSgLet { grade, argument, tail }: PreSgLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(usize, StaticTerm, Binder<Label, B, 2>) -> B,
	) -> Result<B, ElaborationError> {
		let argument_range = argument.range;
		let (tm, ty, _) = self.amplify(grade).erase_if(grade == 0).synthesize_static(argument)?;
		let StaticValue::IndexedSum { base_copy, base, family_copy, family } = ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(argument_range));
		};
		let pair_value = tm.clone().evaluate_in(&self.environment);
		let base = (*base).clone();
		let basepoint = pair_value.clone().field(Field::Base);
		let fiber = family.evaluate_with([basepoint.clone()]);
		let fiberpoint = pair_value.field(Field::Fiber);
		let tail_b = self
			.extend(tail)
			.alias_static(false, grade.into(), base_copy, base, basepoint)
			.alias_static(false, grade.into(), family_copy, fiber, fiberpoint)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, tm, tail_b))
	}

	fn elaborate_dynamic_sg_let<A, B>(
		&mut self,
		PreSgLet { grade, argument, tail }: PreSgLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(usize, [Box<KindTerm>; 2], DynamicTerm, Binder<Label, B, 2>) -> B,
	) -> Result<B, ElaborationError> {
		let argument_range = argument.range;
		let (tm, ty, _) = self.amplify(grade).erase_if(grade == 0).synthesize_dynamic(argument)?;
		let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(argument_range));
		};
		let pair_value = tm.clone().evaluate_in(&self.environment);
		let base = (*base).clone();
		let basepoint = pair_value.clone().field(Field::Base);
		let fiber = family.evaluate_with([basepoint.clone()]);
		let fiberpoint = pair_value.field(Field::Fiber);
		let tail_b = self
			.extend(tail)
			.alias_dynamic(false, grade.into(), (*base_kind).clone(), base, basepoint)
			.alias_dynamic(false, grade.into(), (*family_kind).clone(), fiber, fiberpoint)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		let kinds = [base_kind, family_kind].map(|x| x.unevaluate_in(self.len()).into());

		Ok(produce_let(grade, kinds, tm, tail_b))
	}
}

struct PreLet {
	grade: Option<Cost>,
	ty: Expression,
	argument: Expression,
	tail: Binder<ParsedLabel, Box<Expression>>,
}

struct PreExpLet {
	grade: Cost,
	grade_argument: Cost,
	argument: Expression,
	tail: Binder<ParsedLabel, Box<Expression>>,
}

struct PreSgLet {
	grade: usize,
	argument: Expression,
	tail: Binder<ParsedLabel, Box<Expression>, 2>,
}
