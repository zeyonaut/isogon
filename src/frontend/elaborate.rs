use std::{
	ops::{Deref, DerefMut},
	rc::Rc,
};

use crate::{
	common::{bind, ArraySize, Binder, Cost, Cpy, Field, Fragment, Index, Label, Level, Name},
	frontend::{
		conversion::Conversion as _,
		evaluate::{Evaluate as _, EvaluateWith as _},
		unevaluate::Unevaluate as _,
	},
	ir::{
		presyntax::{
			Constructor, Expression, Former, IrrefutablePattern, ParsedLabel, ParsedPreterm, ParsedProgram,
			Pattern, Preterm, Projector,
		},
		semantics::{DynamicNeutral, DynamicValue, Environment, KindValue, StaticNeutral, StaticValue, Value},
		syntax::{CoreProgram, DynamicTerm, KindTerm, StaticTerm},
	},
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(program: ParsedProgram) -> Result<CoreProgram, ElaborationError> {
	let mut context = Context::empty(program.fragment);
	if let Some((input, domain)) = program.input {
		let (domain, domain_kind) = context.elaborate_dynamic_type(domain)?;
		let domain_value = domain.evaluate();
		let (binder, note) = context
			.extend(bind([input], program.expr))
			.bind_dynamic(false, 1.into(), domain_kind.clone(), domain_value)
			.map(|context, body| context.synthesize_dynamic(body))?
			.retract_dynamic();
		Ok(CoreProgram {
			input: Some((input.label, domain_kind)),
			term: binder.body,
			ty: note.ty,
			kind: note.kind,
		})
	} else {
		let term = context.synthesize_dynamic(program.expr)?;
		Ok(CoreProgram { input: None, term: term.term, ty: term.note.ty, kind: term.note.kind })
	}
}

#[derive(Debug, Clone)]
pub struct ElaborationError {
	pub range: (usize, usize),
	pub kind: ElaborationErrorKind,
}

#[derive(Debug, Clone)]
pub enum ExpectedFormer {
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
pub enum ElaborationErrorKind {
	ExpectedStaticFoundDynamicVariable,
	ExpectedDynamicFoundStaticVariable,
	UsedNonCrispLockedVariable,
	VariableHasUsesLeft { label: Label, remaining_usage: u64 },
	SynthesizedLambda,
	AttemptedMaterialization,
	InvalidFormer,
	InvalidConstructor,
	InvalidProjector,
	ExpectedFormer(ExpectedFormer),
	SynthesizedFormer(ExpectedFormer),
	StaticBidirectionalMismatch { synthesized: StaticTerm, expected: StaticTerm },
	DynamicBidirectionalMismatch { synthesized: DynamicTerm, expected: DynamicTerm },
	CouldNotConvertDynamic(DynamicTerm, DynamicTerm),
	InvalidCaseSplit,
	InvalidCaseSplitScrutineeType,
	CouldNotSynthesizeStatic,
	CouldNotSynthesizeDynamic,
	NotInScope,
	FiberAxesDependentOnBasepoint,
	RanOutOfVariableUses { label: Label, extra_usage: Cost },
	WrongArity,
	InvalidArgumentCount,
	InvalidStaticUniverse,
	InvalidGrade,
	InvalidIrrefutablePattern,
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
	previous_fragment: Fragment,
}

impl<'c> AmplifiedContext<'c> {
	fn new(ctx: &'c mut Context, amplifier: Cost) -> Self {
		let previous_fragment = ctx.fragment;
		if amplifier == Cost::Fin(0) {
			ctx.fragment = Fragment::Logical;
		}
		ctx.amplifiers.push((ctx.len().0, amplifier));
		Self { context: ctx, previous_fragment }
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
	fn drop(&mut self) {
		self.context.fragment = self.previous_fragment;
		self.context.amplifiers.pop();
	}
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
		let grade = grade * (self.context.fragment as u64).into();
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
		let grade = grade * (self.context.fragment as u64).into();
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
		let grade = grade * (self.context.fragment as u64).into();
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
		let grade = grade * (self.context.fragment as u64).into();
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
					.ok_or(ElaborationErrorKind::VariableHasUsesLeft { label: p.label, remaining_usage: grade })
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

		let label = self.tys[level].0;
		if let Cost::Fin(grade) = &mut self.tys[level].1.grade {
			if let Cost::Fin(usage) = usage {
				*grade = grade
					.checked_sub(usage)
					.ok_or(ElaborationErrorKind::RanOutOfVariableUses { label, extra_usage: Cost::Fin(usage) })?;
			} else {
				return Err(ElaborationErrorKind::RanOutOfVariableUses { label, extra_usage: Cost::Inf });
			}
		}

		Ok(())
	}

	pub fn erase(&mut self) -> ErasedContext<'_> { ErasedContext::new(self, Fragment::Logical) }

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

	fn synthesize_static(&mut self, expr: Expression) -> Result<AnnotatedStaticTerm, ElaborationError> {
		self.elaborate_static(expr, None)
	}

	fn verify_static(&mut self, expr: Expression, note: StaticNote) -> Result<StaticTerm, ElaborationError> {
		self.elaborate_static(expr, Some(note)).map(|x| x.term)
	}

	fn elaborate_static(
		&mut self,
		expr: Expression,
		note: Option<StaticNote>,
	) -> Result<AnnotatedStaticTerm, ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match (preterm, note) {
			// Variables.
			(Preterm::Variable(name), None) => 'var: {
				for (i, (name_1, entry)) in self.tys.iter().rev().enumerate() {
					if &Some(name) == name_1 {
						if let ContextType::Static(ty, c) = &entry.ty {
							let result =
								StaticTerm::Variable(Some(name), Index(i)).annotate(StaticNote::new(ty.clone(), *c));
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
			(Preterm::Let { is_meta: true, grade, ty, argument, pattern, tail }, note) => match pattern {
				IrrefutablePattern::Label(label) => self.elaborate_static_let(
					PreLet { grade, ty: ty.map(|x| *x), argument: *argument, tail: bind([label], tail) },
					note,
					Self::elaborate_static,
					|grade, ty, argument, tail| {
						let (tail, note) = tail.retract_static();
						StaticTerm::Let { grade, ty: ty.into(), argument: argument.into(), tail: tail.map_into() }
							.annotate(note)
					},
				)?,

				// Repeated programs.
				IrrefutablePattern::Exp(grade_argument, label) => self.elaborate_static_exp_let(
					PreExpLet {
						grade: grade.unwrap_or(1.into()),
						grade_argument,
						argument: *argument,
						tail: bind([label], tail),
					},
					note,
					Self::elaborate_static,
					|grade, grade_argument, argument, tail| {
						let (tail, note) = tail.retract_static();
						StaticTerm::ExpLet {
							grade,
							grade_argument,
							argument: argument.into(),
							tail: tail.map_into(),
						}
						.annotate(note)
					},
				)?,

				// Dependent pairs.
				IrrefutablePattern::Pair(labels) => self.elaborate_static_sg_let(
					PreSgLet { grade: grade.unwrap_or(1.into()), argument: *argument, tail: bind(labels, tail) },
					note,
					Self::elaborate_static,
					|grade, argument, tail| {
						let (tail, note) = tail.retract_static();
						StaticTerm::SgLet { grade, argument: argument.into(), tail: tail.map_into() }.annotate(note)
					},
				)?,
			},

			// Quoting.
			(Preterm::SwitchLevel(quotee), None) => {
				let quotee = self.synthesize_dynamic(*quotee)?;
				StaticTerm::Quote(quotee.term.into()).annotate(quotee.note.lift())
			}
			(Preterm::SwitchLevel(quotee), Some(note)) => {
				let StaticValue::Lift { kind, ty: liftee } = &note.ty else {
					return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
				};
				let quotee = self
					.elaborate_dynamic(*quotee, Some(DynamicNote::new((*liftee).clone(), (**kind).clone())))?;
				StaticTerm::Quote(quotee.term.into()).annotate(note)
			}

			// Dependent functions.
			(Preterm::Pi { fragment, base, family }, None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				let (base, base_copy) = self.elaborate_static_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_copy) = self
					.extend(family)
					.bind_static(false, 0.into(), base_copy, base_value)
					.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
				StaticTerm::Pi { fragment, base_copy, base: base.into(), family_copy, family: family.map_into() }
					.annotate(StaticNote::universe(family_copy))
			}
			(Preterm::Lambda { .. }, None) =>
				return Err(ElaborationErrorKind::SynthesizedLambda.at(expr.range)),
			(Preterm::Lambda { body }, Some(note)) => {
				let StaticValue::IndexedProduct { fragment, base_copy, base, family_copy, family } = &note.ty
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let body = self
					.extend(body)
					.bind_static(false, (*fragment).into(), *base_copy, base.as_ref().clone())
					.map(|ctx, body| {
						ctx.verify_static(*body, StaticNote::new(family.evaluate_with([ctx.var(0)]), *family_copy))
					})?;
				StaticTerm::Function(*fragment, body.map_into()).annotate(note)
			}
			(Preterm::Call { callee, argument }, None) => {
				let callee = self.synthesize_static(*callee)?;
				let StaticValue::IndexedProduct { fragment, base_copy, base, family_copy, family } =
					callee.note.ty
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let argument = self
					.amplify(fragment)
					.verify_static(*argument, StaticNote::new((*base).clone(), base_copy))?;
				StaticTerm::Apply { scrutinee: callee.term.into(), argument: argument.clone().into() }.annotate(
					StaticNote::new(family.evaluate_with([argument.evaluate_in(&self.environment)]), family_copy),
				)
			}

			// Dependent pairs.
			(Preterm::Sg { base, family }, None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				let (base, base_copy) = self.elaborate_static_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_copy) = self
					.extend(family)
					.bind_static(false, 0.into(), base_copy, base_value)
					.map_extra(|ctx, body| ctx.elaborate_static_type(*body))?;
				StaticTerm::Sg { base_copy, base: base.into(), family_copy, family: family.map_into() }
					.annotate(StaticNote::universe(base_copy.max(family_copy)))
			}
			(Preterm::Pair { basepoint, fiberpoint }, None) => {
				let basepoint = self.synthesize_static(*basepoint)?;
				let fiberpoint = self.synthesize_static(*fiberpoint)?;
				StaticTerm::Pair { basepoint: basepoint.term.into(), fiberpoint: fiberpoint.term.into() }
					.annotate(StaticNote::product(self.len(), basepoint.note, fiberpoint.note))
			}
			(Preterm::Pair { basepoint, fiberpoint }, Some(note)) => {
				let StaticValue::IndexedSum { base_copy, base, family_copy, family } = &note.ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				let basepoint =
					self.verify_static(*basepoint, StaticNote::new(base.as_ref().clone(), *base_copy))?;
				let basepoint_value = basepoint.clone().evaluate_in(&self.environment);
				let fiberpoint = self.verify_static(
					*fiberpoint,
					StaticNote::new(family.evaluate_with([basepoint_value]), *family_copy),
				)?;
				StaticTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }.annotate(note)
			}

			// Generic type formers.
			(Preterm::Former(former, arguments), None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				match former {
					// Types and universe indices.
					Former::Universe => {
						let [c] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						match c.preterm {
							ParsedPreterm(Preterm::Constructor(Constructor::Cpy(c), v)) if v.is_empty() =>
								StaticTerm::Universe(c).annotate(StaticNote::universe(Cpy::Tr)),
							_ => return Err(ElaborationErrorKind::InvalidStaticUniverse.at(expr.range)),
						}
					}
					Former::Copy => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						StaticTerm::Cpy.annotate(StaticNote::universe(Cpy::Tr))
					}
					Former::Repr => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						StaticTerm::Repr.annotate(StaticNote::universe(Cpy::Tr))
					}

					// Quoting.
					Former::Lift => {
						let [liftee] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (liftee, kind) = self.elaborate_dynamic_type(liftee)?;
						StaticTerm::Lift { liftee: liftee.into(), kind: kind.unevaluate_in(self.len()).into() }
							.annotate(StaticNote::universe(Cpy::Nt))
					}

					// Repeated programs.
					Former::Exp(grade) => {
						let [ty] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (ty, c) = self.elaborate_static_type(ty)?;

						StaticTerm::Exp(grade, c, ty.into()).annotate(StaticNote::universe(if grade == 0.into() {
							Cpy::Tr
						} else {
							c
						}))
					}

					// Enumerated numbers.
					Former::Enum(card) => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						StaticTerm::Enum(card).annotate(StaticNote::universe(Cpy::Tr))
					}

					// Natural numbers.
					Former::Nat => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						StaticTerm::Nat.annotate(StaticNote::universe(Cpy::Tr))
					}

					// Invalid former.
					_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
				}
			}

			// Generic term constructors.
			(Preterm::Constructor(constructor, arguments), None) => match constructor {
				// Universe indices.
				Constructor::Cpy(c) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					match c {
						Cpy::Tr => StaticTerm::CpyMax(vec![]),
						Cpy::Nt => StaticTerm::CpyNt,
					}
					.annotate(StaticNote::cpy())
				}
				Constructor::CpyMax => StaticTerm::CpyMax(
					arguments
						.into_iter()
						.map(|a| self.verify_static(a, StaticNote::cpy()))
						.collect::<Result<_, _>>()?,
				)
				.annotate(StaticNote::cpy()),

				Constructor::ReprAtom(r) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					StaticTerm::ReprAtom(r).annotate(StaticNote::repr())
				}
				Constructor::ReprExp(grade) => {
					let [c, r] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let c = self.verify_static(c, StaticNote::cpy())?;
					let r = self.verify_static(r, StaticNote::repr())?;
					match grade {
						0 => StaticTerm::ReprAtom(None),
						1 => r,
						grade =>
							StaticTerm::ReprExp { len: ArraySize(grade), kind: KindTerm { copy: c, repr: r }.into() },
					}
					.annotate(StaticNote::repr())
				}
				Constructor::ReprPair => {
					let [r0, r1] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let r0 = self.verify_static(r0, StaticNote::repr())?;
					let r1 = self.verify_static(r1, StaticNote::repr())?;
					StaticTerm::ReprPair(r0.into(), r1.into()).annotate(StaticNote::repr())
				}

				// Repeated programs.
				Constructor::Exp(grade) => {
					let [inner] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let inner = self.amplify(grade).synthesize_static(inner)?;
					StaticTerm::Repeat(grade, inner.term.into()).annotate(inner.note.exp(grade))
				}

				// Enumerated numbers.
				Constructor::Enum(k, v) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					StaticTerm::EnumValue(k, v).annotate(StaticNote::enu(k))
				}

				// Natural numbers.
				Constructor::Num(n) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					StaticTerm::Num(n).annotate(StaticNote::nat())
				}
				Constructor::Suc => {
					let [prev] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let prev = self.verify_static(prev, StaticNote::nat())?;
					if let StaticTerm::Num(p) = prev {
						StaticTerm::Num(p + 1).annotate(StaticNote::nat())
					} else {
						StaticTerm::Suc(prev.into()).annotate(StaticNote::nat())
					}
				}

				// Invalid constructor.
				_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
			},

			// Generic projectors.
			(Preterm::Project(scrutinee, projector), None) => match projector {
				// Repeated programs.
				Projector::Exp => {
					if self.fragment != Fragment::Logical {
						return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
					}
					let scrutinee = self.synthesize_static(*scrutinee)?;
					let StaticValue::Exp(_, c, ty) = scrutinee.note.ty else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(expr.range));
					};
					StaticTerm::ExpProject(scrutinee.term.into()).annotate(StaticNote::new(ty.as_ref().clone(), c))
				}

				// Dependent pairs.
				Projector::Field(field) => {
					if self.fragment != Fragment::Logical {
						return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
					}
					let scrutinee = self.synthesize_static(*scrutinee)?;
					let StaticValue::IndexedSum { base_copy, base, family_copy, family } = scrutinee.note.ty
					else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
					};
					match field {
						Field::Base => StaticTerm::SgField(scrutinee.term.into(), field)
							.annotate(StaticNote::new(base.as_ref().clone(), base_copy)),
						Field::Fiber =>
							StaticTerm::SgField(scrutinee.term.clone().into(), field).annotate(StaticNote::new(
								family.evaluate_with([StaticTerm::SgField(
									scrutinee.term.clone().into(),
									Field::Base,
								)
								.evaluate_in(&self.environment)]),
								family_copy,
							)),
					}
				}

				// Invalid projector.
				_ => return Err(ElaborationErrorKind::InvalidProjector.at(expr.range)),
			},

			// Generic case splits.
			(Preterm::Split { scrutinee, is_cast: false, motive, cases }, None) => {
				let scrutinee = self.synthesize_static(*scrutinee)?;
				let scrutinee_value = scrutinee.term.clone().evaluate_in(&self.environment);
				match scrutinee.note.ty {
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
								self.amplify(if card <= 1 { Cost::Fin(1) } else { Cost::Inf }).verify_static(
									case,
									StaticNote::new(
										motive_value.evaluate_with([StaticValue::EnumValue(card, v)]),
										motive_copy,
									),
								)?,
							)
						}
						StaticTerm::CaseEnum {
							scrutinee: scrutinee.term.into(),
							motive: motive_term.map_into(),
							cases: new_cases,
						}
						.annotate(StaticNote::new(motive_value.evaluate_with([scrutinee_value]), motive_copy))
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
						let case_nil = self.verify_static(
							case_nil,
							StaticNote::new(motive_value.evaluate_with([StaticValue::Num(0)]), motive_c),
						)?;
						let case_suc = self
							.amplify(Cost::Inf)
							.extend(case_suc)
							.bind_static(false, Cost::Inf, Cpy::Tr, StaticValue::Nat)
							.bind_static_with(false, 1.into(), motive_c, |ctx| {
								motive_value.evaluate_with([ctx.var(0)])
							})
							.map(|ctx, body| {
								ctx.verify_static(
									body,
									StaticNote::new(
										motive_value.evaluate_with([ctx.var::<StaticValue>(1).suc()]),
										motive_c,
									),
								)
							})?;
						StaticTerm::CaseNat {
							scrutinee: scrutinee.term.into(),
							motive: motive.map_into(),
							case_nil: case_nil.into(),
							case_suc: case_suc.map_into(),
						}
						.annotate(StaticNote::new(motive_value.evaluate_with([scrutinee_value]), motive_c))
					}

					// Invalid case split.
					_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
				}
			}

			// Switch directions
			(term, Some(note)) => {
				let term = self.synthesize_static(term.at(expr.range))?;
				if self.len().can_convert(&term.note.ty, &note.ty) {
					term
				} else {
					return Err(
						ElaborationErrorKind::StaticBidirectionalMismatch {
							synthesized: term.note.ty.unevaluate_in(self.len()),
							expected: note.ty.unevaluate_in(self.len()),
						}
						.at(expr.range),
					);
				}
			}

			// Synthesis failure.
			(_, None) => return Err(ElaborationErrorKind::CouldNotSynthesizeStatic.at(expr.range)),
		})
	}

	fn synthesize_dynamic(&mut self, expr: Expression) -> Result<AnnotatedDynamicTerm, ElaborationError> {
		self.elaborate_dynamic(expr, None)
	}

	fn verify_dynamic(
		&mut self,
		expr: Expression,
		note: DynamicNote,
	) -> Result<DynamicTerm, ElaborationError> {
		self.elaborate_dynamic(expr, Some(note)).map(|x| x.term)
	}

	fn elaborate_dynamic(
		&mut self,
		expr: Expression,
		note: Option<DynamicNote>,
	) -> Result<AnnotatedDynamicTerm, ElaborationError> {
		let ParsedPreterm(preterm) = expr.preterm;
		Ok(match (preterm, note) {
			// Variables.
			(Preterm::Variable(name), None) => 'var: {
				for (i, (name_1, entry)) in self.tys.iter().rev().enumerate() {
					if &Some(name) == name_1 {
						if let ContextType::Dynamic(ty, kind) = &entry.ty {
							let result = DynamicTerm::Variable(Some(name), Index(i))
								.annotate(DynamicNote::new(ty.clone(), kind.clone()));
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
			(Preterm::Let { is_meta, grade, ty, argument, pattern, tail }, note) =>
				if is_meta {
					let IrrefutablePattern::Label(label) = pattern else {
						return Err(ElaborationErrorKind::InvalidIrrefutablePattern.at(expr.range));
					};
					self.elaborate_static_let(
						PreLet { grade, ty: ty.map(|x| *x), argument: *argument, tail: bind([label], tail) },
						note,
						|ctx, tail_body, note| ctx.elaborate_dynamic(tail_body, note),
						|grade, ty, argument, tail| {
							let (tail, note) = tail.retract_dynamic();
							DynamicTerm::Def {
								grade,
								ty: ty.into(),
								argument: argument.into(),
								tail: tail.map_into(),
							}
							.annotate(note)
						},
					)?
				} else {
					match pattern {
						IrrefutablePattern::Label(label) => self.elaborate_dynamic_let(
							PreLet { grade, ty: ty.map(|x| *x), argument: *argument, tail: bind([label], tail) },
							note,
							Self::elaborate_dynamic,
							|grade, ty, argument_kind, argument, tail| {
								let (tail, note) = tail.retract_dynamic();
								DynamicTerm::Let {
									grade,
									ty: ty.into(),
									argument_kind: argument_kind.into(),
									argument: argument.into(),
									tail: tail.map_into(),
								}
								.annotate(note)
							},
						)?,

						// Repeated programs.
						IrrefutablePattern::Exp(grade_argument, label) => self.elaborate_dynamic_exp_let(
							PreExpLet {
								grade: grade.unwrap_or(1.into()),
								grade_argument,
								argument: *argument,
								tail: bind([label], tail),
							},
							note,
							Self::elaborate_dynamic,
							|grade, grade_argument, argument, kind_arg, tail| {
								let (tail, note) = tail.retract_dynamic();
								DynamicTerm::ExpLet {
									grade,
									grade_argument,
									argument: argument.into(),
									kind: kind_arg.into(),
									tail: tail.map_into(),
								}
								.annotate(note)
							},
						)?,

						// Dependent pairs.
						IrrefutablePattern::Pair(labels) => self.elaborate_dynamic_sg_let(
							PreSgLet {
								grade: grade.unwrap_or(1.into()),
								argument: *argument,
								tail: bind(labels, tail),
							},
							note,
							Self::elaborate_dynamic,
							|grade, kinds, argument, tail| {
								let (tail, note) = tail.retract_dynamic();
								DynamicTerm::SgLet { grade, kinds, argument: argument.into(), tail: tail.map_into() }
									.annotate(note)
							},
						)?,
					}
				},

			// Splicing.
			(Preterm::SwitchLevel(splicee), None) => {
				let splicee = self.synthesize_static(*splicee)?;
				let StaticValue::Lift { ty: liftee, kind } = splicee.note.ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
				};
				DynamicTerm::Splice(splicee.term.into()).annotate(DynamicNote::new(liftee, (*kind).clone()))
			}
			(Preterm::SwitchLevel(splicee), Some(note)) => {
				let splicee = self.verify_static(*splicee, note.clone().lift())?;
				DynamicTerm::Splice(splicee.into()).annotate(note)
			}

			// Dependent functions.
			(Preterm::Pi { fragment, base, family }, None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				let (base, base_kind) = self.elaborate_dynamic_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_kind) = self
					.extend(family)
					.bind_dynamic(false, 0.into(), base_kind.clone(), base_value)
					.map(|ctx, body| ctx.elaborate_dynamic_type(*body))?
					.retract();
				let Some(family_kind) = family_kind.try_unevaluate_in(self.len()) else {
					return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
				};
				DynamicTerm::Pi {
					fragment,
					base_kind: base_kind.unevaluate_in(self.len()).into(),
					base: base.into(),
					family_kind: family_kind.into(),
					family: family.map_into(),
				}
				.annotate(DynamicNote::universe(KindValue::fun()))
			}
			(Preterm::Lambda { .. }, None) =>
				return Err(ElaborationErrorKind::SynthesizedLambda.at(expr.range)),
			(Preterm::Lambda { body }, Some(note)) => {
				let DynamicValue::IndexedProduct { fragment, base_kind, base, family_kind, family } = &note.ty
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let body = self
					.extend(body)
					.bind_dynamic(false, (*fragment).into(), (**base_kind).clone(), base.as_ref().clone())
					.map(|ctx, body| {
						ctx.verify_dynamic(
							*body,
							DynamicNote::new(family.evaluate_with([ctx.var(0)]), (**family_kind).clone()),
						)
					})?
					.map_into();
				DynamicTerm::Function {
					fragment: *fragment,
					body,
					domain_kind: Some(base_kind.unevaluate_in(self.len()).into()),
					codomain_kind: Some(family_kind.unevaluate_in(self.len()).into()),
				}
				.annotate(note)
			}
			(Preterm::Call { callee, argument }, None) => {
				let scrutinee = self.synthesize_dynamic(*callee)?;
				let DynamicValue::IndexedProduct { fragment, base_kind, base, family_kind, family } =
					scrutinee.note.ty
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
				};
				let argument = self
					.amplify(fragment)
					.verify_dynamic(*argument, DynamicNote::new((*base).clone(), (*base_kind).clone()))?;
				let argument_value = argument.clone().evaluate_in(&self.environment);
				DynamicTerm::Apply {
					scrutinee: scrutinee.term.into(),
					fragment: Some(fragment),
					argument: argument.into(),
					family_kind: Some(family_kind.unevaluate_in(self.len()).into()),
				}
				.annotate(DynamicNote::new(family.evaluate_with([argument_value]), (*family_kind).clone()))
			}

			// Dependent pairs.
			(Preterm::Sg { base, family }, None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				let (base, base_kind) = self.elaborate_dynamic_type(*base)?;
				let base_value = base.clone().evaluate_in(&self.environment);
				let (family, family_kind) = self
					.extend(family)
					.bind_dynamic(false, 0.into(), base_kind.clone(), base_value)
					.map_extra(|ctx, body| ctx.elaborate_dynamic_type(*body))?;
				let kind = KindValue::pair(self.len(), base_kind.clone(), family_kind.clone());
				let Some(family_kind) = family_kind.try_unevaluate_in(self.len()) else {
					return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
				};
				DynamicTerm::Sg {
					base_kind: base_kind.unevaluate_in(self.len()).into(),
					base: base.into(),
					family_kind: family_kind.into(),
					family: family.map_into(),
				}
				.annotate(DynamicNote::new(DynamicValue::Universe { kind: kind.into() }, KindValue::ty()))
			}
			(Preterm::Pair { basepoint, fiberpoint }, None) => {
				let basepoint = self.synthesize_dynamic(*basepoint)?;
				let fiberpoint = self.synthesize_dynamic(*fiberpoint)?;
				DynamicTerm::Pair { basepoint: basepoint.term.into(), fiberpoint: fiberpoint.term.into() }
					.annotate(DynamicNote::product(self.len(), basepoint.note, fiberpoint.note))
			}
			(Preterm::Pair { basepoint, fiberpoint }, Some(note)) => {
				let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = &note.ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				let basepoint = self.verify_dynamic(
					*basepoint,
					DynamicNote::new(base.as_ref().clone(), base_kind.as_ref().clone()),
				)?;
				let basepoint_value = basepoint.clone().evaluate_in(&self.environment);
				let fiberpoint = self.verify_dynamic(
					*fiberpoint,
					DynamicNote::new(family.evaluate_with([basepoint_value]), family_kind.as_ref().clone()),
				)?;
				DynamicTerm::Pair { basepoint: basepoint.into(), fiberpoint: fiberpoint.into() }.annotate(note)
			}

			// Generic type formers.
			(Preterm::Former(former, arguments), None) => {
				if self.fragment != Fragment::Logical {
					return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
				}
				match former {
					// Types.
					Former::Universe => {
						let [copy, repr] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let copy = self.verify_static(copy, StaticNote::cpy())?;
						let repr = self.verify_static(repr, StaticNote::repr())?;
						DynamicTerm::Universe { kind: KindTerm { copy, repr }.into() }
							.annotate(DynamicNote::universe(KindValue::ty()))
					}

					// Repeated programs.
					Former::Exp(Cost::Fin(grade)) => {
						let [ty] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (ty, kind) = self.elaborate_dynamic_type(ty)?;
						DynamicTerm::Exp(grade, kind.unevaluate_in(self.len()).into(), ty.into())
							.annotate(DynamicNote::universe(kind.exp(grade)))
					}

					// Enumerated numbers.
					Former::Enum(card) => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						DynamicTerm::Enum(card).annotate(DynamicNote::universe(KindValue::enu()))
					}

					// Paths.
					Former::Id => {
						let [ty, x, y] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (ty, kind) = self.elaborate_dynamic_type(ty)?;
						let ty_value = ty.clone().evaluate_in(&self.environment);
						let x = self.verify_dynamic(x, DynamicNote::new(ty_value.clone(), kind.clone()))?;
						let y = self.verify_dynamic(y, DynamicNote::new(ty_value, kind.clone()))?;
						DynamicTerm::Id {
							kind: kind.unevaluate_in(self.len()).into(),
							space: ty.into(),
							left: x.into(),
							right: y.into(),
						}
						.annotate(DynamicNote::universe(KindValue::path()))
					}

					// Natural numbers.
					Former::Nat => {
						let [] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						DynamicTerm::Nat.annotate(DynamicNote::universe(KindValue::nat()))
					}

					// Wrappers.
					Former::Bx => {
						let [ty] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (ty, kind) = self.elaborate_dynamic_type(ty)?;
						DynamicTerm::Bx { kind: kind.unevaluate_in(self.len()).into(), inner: ty.into() }
							.annotate(DynamicNote::universe(KindValue::ptr()))
					}
					Former::Wrap => {
						let [ty] = arguments
							.try_into()
							.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
						let (ty, kind) = self.elaborate_dynamic_type(ty)?;
						DynamicTerm::Wrap { inner: ty.into(), kind: kind.unevaluate_in(self.len()).into() }
							.annotate(DynamicNote::universe(kind.wrap()))
					}

					// Invalid former.
					_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
				}
			}

			// Generic term constructors.
			(Preterm::Constructor(constructor, arguments), note) => match (constructor, note) {
				// Repeated programs.
				(Constructor::Exp(Cost::Fin(grade)), None) => {
					let [inner] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let inner = self.amplify(grade).synthesize_dynamic(inner)?;
					DynamicTerm::Repeat {
						grade,
						kind: Some(inner.note.kind.unevaluate_in(self.len()).into()),
						term: inner.term.into(),
					}
					.annotate(inner.note.exp(grade))
				}

				// Enumerated numbers.
				(Constructor::Enum(k, v), None) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					DynamicTerm::EnumValue(k, v).annotate(DynamicNote::enu(k))
				}

				// Paths.
				(Constructor::Refl, Some(note)) => {
					if self.fragment != Fragment::Logical {
						return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
					}
					let DynamicValue::Id { left, right, .. } = &note.ty else {
						return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Id).at(expr.range));
					};
					if !(self.len().can_convert(&**left, right)) {
						return Err(
							ElaborationErrorKind::CouldNotConvertDynamic(
								left.unevaluate_in(self.len()),
								right.unevaluate_in(self.len()),
							)
							.at(expr.range),
						);
					}
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					DynamicTerm::Refl.annotate(note)
				}

				// Natural numbers.
				(Constructor::Num(n), None) => {
					let [] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					DynamicTerm::Num(n).annotate(DynamicNote::nat())
				}
				(Constructor::Suc, None) => {
					let [prev] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					let prev = self.verify_dynamic(prev, DynamicNote::nat())?;
					if let DynamicTerm::Num(p) = prev {
						DynamicTerm::Num(p + 1).annotate(DynamicNote::nat())
					} else {
						DynamicTerm::Suc(prev.into()).annotate(DynamicNote::nat())
					}
				}

				// Wrappers.
				(Constructor::Bx, note) => {
					let [inner] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					if let Some(note) = note {
						let Some(inner_note) = note.get_if_bx() else {
							return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Bx).at(expr.range));
						};
						let inner = self.verify_dynamic(inner, inner_note)?;
						DynamicTerm::BxValue(inner.into()).annotate(note)
					} else {
						let inner = self.synthesize_dynamic(inner)?;
						DynamicTerm::BxValue(inner.term.into()).annotate(inner.note.bx())
					}
				}
				(Constructor::Wrap, note) => {
					let [inner] = arguments
						.try_into()
						.map_err(|_| ElaborationErrorKind::InvalidArgumentCount.at(expr.range))?;
					if let Some(note) = note {
						let Some(inner_note) = note.get_if_wrap() else {
							return Err(
								ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Wrap).at(expr.range),
							);
						};
						let inner = self.verify_dynamic(inner, inner_note)?;
						DynamicTerm::WrapValue(inner.into()).annotate(note)
					} else {
						let inner = self.synthesize_dynamic(inner)?;
						DynamicTerm::WrapValue(inner.term.into()).annotate(inner.note.wrap())
					}
				}

				// Invalid constructor.
				(_, None) => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
				(constructor, Some(note)) =>
					return self.switch_directions_dynamic(
						Preterm::Constructor(constructor, arguments).at(expr.range),
						note,
					),
			},

			// Generic projectors.
			(Preterm::Project(scrutinee, projector), None) => match projector {
				// Repeated programs.
				Projector::Exp => {
					if self.fragment != Fragment::Logical {
						return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
					}
					let scrutinee = self.synthesize_dynamic(*scrutinee)?;
					let Some(inner_note) = scrutinee.note.get_if_exp() else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(expr.range));
					};
					DynamicTerm::ExpProject(scrutinee.term.into()).annotate(inner_note)
				}

				// Dependent pairs.
				Projector::Field(field) => {
					if self.fragment != Fragment::Logical {
						return Err(ElaborationErrorKind::AttemptedMaterialization.at(expr.range));
					}
					let scrutinee = self.synthesize_dynamic(*scrutinee)?;
					let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = scrutinee.note.ty
					else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
					};
					let basepoint =
						DynamicTerm::SgField { scrutinee: scrutinee.term.clone().into(), field: Field::Base };
					match field {
						Field::Base =>
							basepoint.annotate(DynamicNote::new(base.as_ref().clone(), (*base_kind).clone())),
						Field::Fiber => DynamicTerm::SgField { scrutinee: scrutinee.term.into(), field }.annotate(
							DynamicNote::new(
								family.evaluate_with([basepoint.evaluate_in(&self.environment)]),
								(*family_kind).clone(),
							),
						),
					}
				}

				// Wrappers.
				Projector::Bx => {
					let outer = self.synthesize_dynamic(*scrutinee)?;
					let Some(inner_note) = outer.note.get_if_bx() else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Bx).at(expr.range));
					};
					DynamicTerm::BxProject {
						scrutinee: outer.term.into(),
						kind: Some(inner_note.kind.unevaluate_in(self.len()).into()),
					}
					.annotate(inner_note)
				}

				Projector::Wrap => {
					let outer = self.synthesize_dynamic(*scrutinee)?;
					let Some(inner_note) = outer.note.get_if_wrap() else {
						return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Wrap).at(expr.range));
					};
					DynamicTerm::WrapProject {
						scrutinee: outer.term.into(),
						kind: Some(inner_note.kind.unevaluate_in(self.len()).into()),
					}
					.annotate(inner_note)
				}
			},

			// Generic case splits.
			(Preterm::Split { scrutinee, is_cast, motive, cases }, None) => {
				let scrutinee = if is_cast {
					self.erase().synthesize_dynamic(*scrutinee)
				} else {
					self.synthesize_dynamic(*scrutinee)
				}?;
				let scrutinee_value = scrutinee.term.clone().evaluate_in(&self.environment);
				match scrutinee.note.ty {
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
						let Some(_) = motive_kind.try_unevaluate_in(self.len()) else {
							return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
						};
						let motive = motive_term.clone().map_into().evaluate_in(&self.environment);

						let case_refl = self.verify_dynamic(
							case_refl,
							DynamicNote::new(
								motive.evaluate_with([(*left).clone(), DynamicValue::Refl]),
								motive_kind.clone(),
							),
						)?;

						DynamicTerm::CasePath {
							scrutinee: scrutinee.term.into(),
							motive: motive_term.map_into(),
							case_refl: case_refl.into(),
						}
						.annotate(DynamicNote::new(
							motive.evaluate_with([(*right).clone(), scrutinee_value]),
							motive_kind,
						))
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
						let Some(_) = motive_kind.try_unevaluate_in(self.len()) else {
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
								self.amplify(if card <= 1 { Cost::Fin(1) } else { Cost::Inf }).verify_dynamic(
									case,
									DynamicNote::new(
										motive.evaluate_with([DynamicValue::EnumValue(card, v)]),
										motive_kind.clone(),
									),
								)?,
							)
						}
						DynamicTerm::CaseEnum {
							scrutinee: scrutinee.term.into(),
							cases: new_cases,
							motive: motive_term.map_into(),
							motive_kind: Some(motive_kind.unevaluate_in(self.len()).into()),
						}
						.annotate(DynamicNote::new(motive.evaluate_with([scrutinee_value]), motive_kind))
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
						let Some(_) = motive_kind.try_unevaluate_in(self.len()) else {
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
						let case_nil = self.verify_dynamic(
							case_nil,
							DynamicNote::new(
								motive_value.evaluate_with([DynamicValue::Num(0)]),
								motive_kind.clone(),
							),
						)?;
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
									DynamicNote::new(
										motive_value.evaluate_with([ctx.var::<DynamicValue>(1).suc()]),
										motive_kind.clone(),
									),
								)
							})?;
						DynamicTerm::CaseNat {
							scrutinee: scrutinee.term.into(),
							motive_kind: Some(motive_kind.unevaluate_in(self.len()).into()),
							motive: motive_term.map_into(),
							case_nil: case_nil.into(),
							case_suc: case_suc.map_into(),
						}
						.annotate(DynamicNote::new(motive_value.evaluate_with([scrutinee_value]), motive_kind))
					}

					// Invalid case split.
					_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
				}
			}

			// Switch directions.
			(term, Some(note)) => return self.switch_directions_dynamic(term.at(expr.range), note),

			// Elaboration failure.
			(_, None) => return Err(ElaborationErrorKind::CouldNotSynthesizeDynamic.at(expr.range)),
		})
	}

	fn switch_directions_dynamic(
		&mut self,
		expr: Expression,
		note: DynamicNote,
	) -> Result<AnnotatedDynamicTerm, ElaborationError> {
		let range = expr.range;
		let term = self.synthesize_dynamic(expr)?;
		if self.len().can_convert(&term.note.ty, &note.ty) {
			Ok(term.term.annotate(note))
		} else {
			Err(
				ElaborationErrorKind::DynamicBidirectionalMismatch {
					synthesized: term.note.ty.unevaluate_in(self.len()),
					expected: note.ty.unevaluate_in(self.len()),
				}
				.at(range),
			)
		}
	}

	fn elaborate_static_type(&mut self, expr: Expression) -> Result<(StaticTerm, Cpy), ElaborationError> {
		let expr_range = expr.range;
		let term = self.erase().synthesize_static(expr)?;
		let StaticValue::Universe(c) = term.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
		};
		Ok((term.term, c))
	}

	fn elaborate_dynamic_type(
		&mut self,
		expr: Expression,
	) -> Result<(DynamicTerm, KindValue), ElaborationError> {
		let expr_range = expr.range;
		let term = self.erase().synthesize_dynamic(expr)?;
		let DynamicValue::Universe { kind } = term.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Universe).at(expr_range));
		};
		Ok((term.term, (*kind).clone()))
	}

	fn elaborate_static_let<A, B>(
		&mut self,
		PreLet { grade, ty, argument, tail }: PreLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(Cost, StaticTerm, StaticTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let grade = grade.unwrap_or_else(|| if tail.parameter().label.is_some() { 1 } else { 0 }.into());

		let (ty_c, ty_value, ty, argument) = if let Some(ty) = ty {
			let (ty, ty_c) = self.elaborate_static_type(ty)?;
			let ty_value = ty.clone().evaluate_in(&self.environment);
			let argument =
				self.amplify(grade).verify_static(argument, StaticNote::new(ty_value.clone(), ty_c))?;
			(ty_c, ty_value, ty, argument)
		} else {
			let argument = self.amplify(grade).synthesize_static(argument)?;
			let ty = argument.note.ty.unevaluate_in(self.len());
			(argument.note.copy, argument.note.ty, ty, argument.term)
		};

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
		produce_let: impl FnOnce(u64, DynamicTerm, KindTerm, DynamicTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let grade = grade.unwrap_or_else(|| if tail.parameter().label.is_some() { 1 } else { 0 }.into());
		let Cost::Fin(grade) = grade else {
			return Err(
				ElaborationErrorKind::InvalidGrade.at((tail.parameter().locus, tail.parameter().locus + 1)),
			);
		};
		let (argument_kind, ty_value, ty, argument) = if let Some(ty) = ty {
			let (ty, argument_kind) = self.elaborate_dynamic_type(ty)?;
			let ty_value = ty.clone().evaluate_in(&self.environment);
			let argument = self
				.amplify(grade)
				.verify_dynamic(argument, DynamicNote::new(ty_value.clone(), argument_kind.clone()))?;
			(argument_kind, ty_value, ty, argument)
		} else {
			let argument = self.amplify(grade).synthesize_dynamic(argument)?;
			let ty = argument.note.ty.unevaluate_in(self.len());
			(argument.note.kind, argument.note.ty, ty, argument.term)
		};
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
		let tm = self.amplify(grade).synthesize_static(argument)?;
		let StaticValue::Exp(n, c, ty) = tm.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		};
		if n != grade_argument {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		}
		let rep_value = tm.term.clone().evaluate_in(&self.environment);
		let inner_value = rep_value.clone().exp_project();
		let tail_b = self
			.extend(tail)
			.alias_static(false, grade * grade_argument, c, (*ty).clone(), inner_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, grade_argument, tm.term, tail_b))
	}

	fn elaborate_dynamic_exp_let<A, B>(
		&mut self,
		PreExpLet { grade, grade_argument, argument, tail }: PreExpLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(u64, u64, DynamicTerm, KindTerm, Binder<Label, B>) -> B,
	) -> Result<B, ElaborationError> {
		let (Cost::Fin(grade), Cost::Fin(grade_argument)) = (grade, grade_argument) else {
			return Err(ElaborationErrorKind::InvalidGrade.at(argument.range));
		};
		let argument_range = argument.range;
		let tm = self.amplify(grade).synthesize_dynamic(argument)?;
		let DynamicValue::Exp(n, kind, ty) = tm.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		};
		if n != grade_argument {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Exp).at(argument_range));
		}
		let rep_value = tm.term.clone().evaluate_in(&self.environment);
		let inner_value = rep_value.clone().exp_project();
		let tail_b = self
			.extend(tail)
			.alias_dynamic(false, (grade * grade_argument).into(), (*kind).clone(), (*ty).clone(), inner_value)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, grade_argument, tm.term, kind.unevaluate_in(self.len()), tail_b))
	}

	fn elaborate_static_sg_let<A, B>(
		&mut self,
		PreSgLet { grade, argument, tail }: PreSgLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(Cost, StaticTerm, Binder<Label, B, 2>) -> B,
	) -> Result<B, ElaborationError> {
		let argument_range = argument.range;
		let tm = self.amplify(grade).synthesize_static(argument)?;
		let StaticValue::IndexedSum { base_copy, base, family_copy, family } = tm.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(argument_range));
		};
		let pair_value = tm.term.clone().evaluate_in(&self.environment);
		let base = (*base).clone();
		let basepoint = pair_value.clone().field(Field::Base);
		let fiber = family.evaluate_with([basepoint.clone()]);
		let fiberpoint = pair_value.field(Field::Fiber);
		let tail_b = self
			.extend(tail)
			.alias_static(false, grade, base_copy, base, basepoint)
			.alias_static(false, grade, family_copy, fiber, fiberpoint)
			.map(|ctx, body| elaborate_tail(ctx, *body, tail_a))?;

		Ok(produce_let(grade, tm.term, tail_b))
	}

	fn elaborate_dynamic_sg_let<A, B>(
		&mut self,
		PreSgLet { grade, argument, tail }: PreSgLet,
		tail_a: A,
		elaborate_tail: impl FnOnce(&mut Context, Expression, A) -> Result<B, ElaborationError>,
		produce_let: impl FnOnce(u64, [Box<KindTerm>; 2], DynamicTerm, Binder<Label, B, 2>) -> B,
	) -> Result<B, ElaborationError> {
		let Cost::Fin(grade) = grade else {
			return Err(ElaborationErrorKind::InvalidGrade.at(argument.range));
		};
		let argument_range = argument.range;
		let tm = self.amplify(grade).synthesize_dynamic(argument)?;
		let DynamicValue::IndexedSum { base_kind, base, family_kind, family } = tm.note.ty else {
			return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(argument_range));
		};
		let pair_value = tm.term.clone().evaluate_in(&self.environment);
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

		Ok(produce_let(grade, kinds, tm.term, tail_b))
	}
}

struct PreLet {
	grade: Option<Cost>,
	ty: Option<Expression>,
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
	grade: Cost,
	argument: Expression,
	tail: Binder<ParsedLabel, Box<Expression>, 2>,
}

impl<P, const N: usize> Binder<P, AnnotatedStaticTerm, N> {
	pub fn retract_static(self) -> (Binder<P, StaticTerm, N>, StaticNote) {
		(Binder { parameters: self.parameters, body: self.body.term }, self.body.note)
	}
}

impl<P, const N: usize> Binder<P, AnnotatedDynamicTerm, N> {
	pub fn retract_dynamic(self) -> (Binder<P, DynamicTerm, N>, DynamicNote) {
		(Binder { parameters: self.parameters, body: self.body.term }, self.body.note)
	}
}

impl StaticTerm {
	fn annotate(self, note: StaticNote) -> AnnotatedStaticTerm { AnnotatedStaticTerm { term: self, note } }
}

struct AnnotatedStaticTerm {
	term: StaticTerm,
	note: StaticNote,
}

struct StaticNote {
	ty: StaticValue,
	copy: Cpy,
}

impl StaticNote {
	fn new(ty: StaticValue, copy: Cpy) -> Self { Self { ty, copy } }

	fn universe(copy: Cpy) -> Self { Self::new(StaticValue::Universe(copy), Cpy::Tr) }

	fn cpy() -> Self { Self::new(StaticValue::Cpy, Cpy::Tr) }

	fn repr() -> Self { Self::new(StaticValue::ReprType, Cpy::Tr) }

	fn product(level: Level, left: Self, right: Self) -> Self {
		let family = bind([None], right.ty.unevaluate_in(level + 1)).evaluate();
		Self::new(
			StaticValue::IndexedSum {
				base_copy: left.copy,
				base: left.ty.into(),
				family_copy: right.copy,
				family: family.into(),
			},
			left.copy.max(right.copy),
		)
	}

	fn exp(self, grade: Cost) -> Self {
		Self::new(
			StaticValue::Exp(grade, self.copy, self.ty.into()),
			if grade == 0.into() { Cpy::Tr } else { self.copy },
		)
	}

	fn enu(card: u16) -> Self { Self::new(StaticValue::Enum(card), Cpy::Tr) }

	fn nat() -> Self { Self::new(StaticValue::Nat, Cpy::Tr) }
}

impl DynamicTerm {
	fn annotate(self, note: DynamicNote) -> AnnotatedDynamicTerm { AnnotatedDynamicTerm { term: self, note } }
}

struct AnnotatedDynamicTerm {
	term: DynamicTerm,
	note: DynamicNote,
}

#[derive(Clone)]
struct DynamicNote {
	ty: DynamicValue,
	kind: KindValue,
}

impl DynamicNote {
	fn new(ty: DynamicValue, kind: KindValue) -> Self { Self { ty, kind } }

	fn universe(kind: KindValue) -> Self {
		Self::new(DynamicValue::Universe { kind: kind.into() }, KindValue::ty())
	}

	fn lift(self) -> StaticNote {
		StaticNote::new(StaticValue::Lift { ty: self.ty, kind: self.kind.into() }, Cpy::Nt)
	}

	fn product(level: Level, left: Self, right: Self) -> Self {
		let family = bind([None], right.ty.unevaluate_in(level + 1)).evaluate();
		Self::new(
			DynamicValue::IndexedSum {
				base_kind: left.kind.clone().into(),
				base: left.ty.into(),
				family_kind: right.kind.clone().into(),
				family: family.into(),
			},
			KindValue::pair(level, left.kind, right.kind),
		)
	}

	fn exp(self, grade: u64) -> Self {
		Self::new(DynamicValue::Exp(grade, self.kind.clone().into(), self.ty.into()), self.kind.exp(grade))
	}

	fn enu(card: u16) -> Self { Self::new(DynamicValue::Enum(card), KindValue::enu()) }

	fn nat() -> Self { Self::new(DynamicValue::Nat, KindValue::nat()) }

	fn bx(self) -> Self {
		Self::new(DynamicValue::Bx { inner: self.ty.into(), kind: self.kind.into() }, KindValue::ptr())
	}

	fn wrap(self) -> Self {
		Self::new(
			DynamicValue::Wrap { inner: self.ty.into(), kind: self.kind.clone().into() },
			self.kind.wrap(),
		)
	}

	fn get_if_exp(&self) -> Option<Self> {
		let DynamicValue::Exp(_, kind, ty) = &self.ty else { return None };
		Some(Self::new(ty.as_ref().clone(), kind.as_ref().clone()))
	}

	fn get_if_bx(&self) -> Option<Self> {
		let DynamicValue::Bx { kind, inner: ty } = &self.ty else { return None };
		Some(Self::new(ty.as_ref().clone(), kind.as_ref().clone()))
	}

	fn get_if_wrap(&self) -> Option<Self> {
		let DynamicValue::Wrap { kind, inner: ty } = &self.ty else { return None };
		Some(Self::new(ty.as_ref().clone(), kind.as_ref().clone()))
	}
}

#[cfg(test)]
mod tests {
	use super::*;

	#[test]
	#[should_panic]
	fn test_extension_mismatch() {
		let _ = Context::empty(Fragment::Material)
			.extend(bind(
				[ParsedLabel { locus: 0, label: None }; 2],
				Box::new(Expression {
					range: (0, 0),
					preterm: ParsedPreterm(Preterm::Constructor(Constructor::Num(20), vec![])),
				}),
			))
			.bind_static(false, 1.into(), Cpy::Tr, StaticValue::Nat)
			.map(|_, expr: Box<Expression>| Ok(expr));
	}
}
