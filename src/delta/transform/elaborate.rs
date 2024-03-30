use std::ops::{Deref, DerefMut};

use crate::{
	delta::{
		common::{bind, Binder, Closure, Copyability, Field, Index, Level, Name, ReprAtom},
		ir::{
			presyntax::{Constructor, Expression, Former, Preterm},
			semantics::{
				Conversion, DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue, Value,
			},
			source::LexedSource,
			syntax::{DynamicTerm, StaticTerm},
		},
		transform::{
			autolyze::Autolyze,
			evaluate::{Evaluate, EvaluateWith},
			parse::report_line_error,
			unevaluate::Unevaluate,
		},
	},
	utility::{bx, rc},
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(source: &str, lexed_source: &LexedSource, term: Expression) -> (DynamicTerm, DynamicValue) {
	// TODO: Offer option to choose fragment, rather than force fragment to be 1.
	match synthesize_dynamic(&mut Context::empty(), term, 1) {
		Ok((term, ty, ..)) => (term, ty),
		Err(error) => {
			report_line_error(
				source,
				lexed_source.ranges.get(error.range.0).copied().unwrap_or((source.len(), source.len() + 1)),
				&format!("elaboration error: {:#?}", error.kind),
			);
			panic!();
		}
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
	Rc,
	Wrap,
	Id,
}

#[derive(Debug, Clone)]
enum ElaborationErrorKind {
	LambdaGradeMismatch(usize, usize),
	ExpectedStaticFoundDynamicVariable,
	ExpectedDynamicFoundStaticVariable,
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
	// Type, copyability, representation
	Dynamic(DynamicValue, StaticValue, StaticValue),
}

#[derive(Clone, Debug)]
pub struct ContextEntry {
	grade: Option<usize>,
	ty: ContextType,
}

impl ContextEntry {
	pub fn new(grade: Option<usize>, ty: ContextType) -> Self { Self { grade, ty } }
}

pub struct AmplifiedContext<'c> {
	context: &'c mut Context,
}

impl<'c> AmplifiedContext<'c> {
	fn new(context: &'c mut Context, amplifier: Option<usize>) -> Self {
		context.amplifiers.push((context.len().0, amplifier));
		Self { context }
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
	fn new(context: &'c mut Context, name: Option<Name>, entry: ContextEntry, value: Value) -> Self {
		context.tys.push((name, entry));
		context.environment.push(value);
		Self { context }
	}

	#[must_use]
	fn free(mut self) -> Result<(), ElaborationErrorKind> {
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
	amplifiers: Vec<(usize, Option<usize>)>,
	environment: Environment,
	tys: Vec<(Option<Name>, ContextEntry)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { amplifiers: Vec::new(), environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level { Level(self.environment.0.len()) }

	// Uses a resource.
	#[must_use]
	fn take_index(&mut self, index: usize, fragment: u8) -> Result<(), ElaborationErrorKind> {
		let level = self.tys.len() - (index + 1);
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

	pub fn amplify<'c>(&'c mut self, amplifier: impl Into<Option<usize>>) -> AmplifiedContext<'c> {
		AmplifiedContext::new(self, amplifier.into())
	}

	pub fn bind_static<'c>(
		&'c mut self,
		name: Option<Name>,
		grade: Option<usize>,
		ty: StaticValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(grade, ContextType::Static(ty)),
			Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))),
		)
	}

	pub fn bind_dynamic<'c>(
		&'c mut self,
		name: Option<Name>,
		grade: Option<usize>,
		ty: DynamicValue,
		copy: StaticValue,
		repr: StaticValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(grade, ContextType::Dynamic(ty, copy, repr)),
			Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))),
		)
	}

	pub fn extend_static<'c>(
		&'c mut self,
		name: Option<Name>,
		grade: Option<usize>,
		ty: StaticValue,
		value: StaticValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(grade, ContextType::Static(ty)),
			Value::Static(value),
		)
	}

	pub fn extend_dynamic<'c>(
		&'c mut self,
		name: Option<Name>,
		grade: Option<usize>,
		ty: DynamicValue,
		copy: StaticValue,
		repr: StaticValue,
		value: DynamicValue,
	) -> ExtendedContext<'c> {
		ExtendedContext::new(
			self,
			name,
			ContextEntry::new(grade, ContextType::Dynamic(ty, copy, repr)),
			Value::Dynamic(value),
		)
	}
}

fn synthesize_static(
	context: &mut Context,
	expr: Expression,
	fragment: u8,
) -> Result<(StaticTerm, StaticValue), ElaborationError> {
	Ok(match expr.preterm {
		// Variables.
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in context.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Static(ty) = &entry.ty {
						let result = (StaticTerm::Variable(Some(name), Index(i)), ty.clone());
						context.take_index(i, fragment).map_err(|e| e.at(expr.range))?;
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
			let ty = verify_static(context, *ty, 0, StaticValue::Universe)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_static(&mut context.amplify(grade), *argument, fragment * (grade > 0) as u8, ty_value.clone())?;
			// TODO: Lazy evaluation.
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty) = {
				let mut context = context.extend_static(parameters[0], (grade * fragment as usize).into(), ty_value, argument_value);
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
			let (quotee, quotee_ty, copy, repr) = synthesize_dynamic(context, *quotee, fragment)?;
			(
				StaticTerm::Quote(bx!(quotee)),
				StaticValue::Lift { ty: quotee_ty.into(), copy: copy.into(), repr: repr.into() },
			)
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if fragment == 0 => {
			let base = verify_static(context, *base, 0, StaticValue::Universe)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let [parameter] = family.parameters;
			let family = {
				let mut context = context.bind_static(parameter, None, base_value);
				let family = verify_static(&mut context, *family.body, 0, StaticValue::Universe)?;
				context.free().map_err(|e| e.at(expr.range))?;
				family
			};
			(StaticTerm::Pi(grade.into(), bx!(base), bind([parameter], family)), StaticValue::Universe)
		}
		Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::Call { callee, argument } => {
			let (callee, scrutinee_ty) = synthesize_static(context, *callee, fragment)?;
			let StaticValue::IndexedProduct(grade, base, family) = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument = verify_static(&mut context.amplify(grade), *argument, fragment * (grade > 0) as u8, (*base).clone())?;
			(
				StaticTerm::Apply { scrutinee: bx!(callee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&context.environment)]),
			)
		}
		
		// Other.
		Preterm::Former(former, arguments) => match former {
			// Types and universe indices.
			Former::Universe if fragment == 0 && arguments.is_empty() => (StaticTerm::Universe, StaticValue::Universe),
			Former::Copy if fragment == 0 && arguments.is_empty() => (StaticTerm::CopyabilityType, StaticValue::Universe),
			Former::Repr if fragment == 0 && arguments.is_empty() => (StaticTerm::ReprType, StaticValue::Universe),

			// Quoting.
			Former::Lift => {
				let [liftee] = arguments.try_into().unwrap();
				let (liftee, copy, repr) = elaborate_dynamic_type(context, liftee)?;
				(
					StaticTerm::Lift {
						liftee: liftee.into(),
						copy: copy.unevaluate_in(context.len()).into(),
						repr: repr.unevaluate_in(context.len()).into(),
					},
					StaticValue::Universe,
				)
			}

			// Repeated programs.
			Former::Exp(grade) => {
				let [ty] = arguments.try_into().unwrap();
				let ty = verify_static(context, ty, 0, StaticValue::Universe)?;
				(StaticTerm::Exp(grade, ty.into()), StaticValue::Universe)
			}
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			// Universe indices.
			Constructor::Copyability(c) if fragment == 0 && arguments.is_empty()=>
				(StaticTerm::Copyability(c), StaticValue::CopyabilityType),
			Constructor::CopyMax if fragment == 0 => {
				let [a, b] = arguments.try_into().unwrap();
				let a = verify_static(context, a, 0, StaticValue::CopyabilityType)?;
				let b = verify_static(context, b, 0, StaticValue::CopyabilityType)?;
				(StaticTerm::MaxCopyability(bx!(a), bx!(b)), StaticValue::CopyabilityType)
			}
			Constructor::ReprAtom(r) if fragment == 0 && arguments.is_empty() => (StaticTerm::ReprAtom(r), StaticValue::ReprType),

			// Repeated programs.
			Constructor::Exp(grade) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty) = synthesize_static(context, tm, 0)?;
				(StaticTerm::Exp(grade, tm.into()), StaticValue::Exp(grade, ty.into()))
			}
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},
		
		// Synthesis failure.
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeStatic.at(expr.range)),
	})
}

fn verify_static(
	context: &mut Context,
	expr: Expression,
	fragment: u8,
	ty: StaticValue,
) -> Result<StaticTerm, ElaborationError> {
	Ok(match (expr.preterm, ty) {
		// Quoted programs.
		(Preterm::SwitchLevel(quotee), ty) => {
			let StaticValue::Lift { ty: liftee, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			let quotee = verify_dynamic(context, *quotee, fragment, liftee)?;
			StaticTerm::Quote(bx!(quotee))
		}

		// Dependent functions.
		(Preterm::Lambda { grade, body }, StaticValue::IndexedProduct(grade_v, base, family)) => {
			(grade == grade_v)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_v).at(expr.range))?;
			let parameters = body.parameters;
			let mut context = context.bind_static(parameters[0], (grade * fragment as usize).into(), base.as_ref().clone());
			let basepoint_level = context.len().index(0);
			let body = verify_static(
				&mut context,
				*body.body,
				fragment,
				family.evaluate_with([(parameters[0], basepoint_level).into()]),
			)?;
			context.free().map_err(|e| e.at(expr.range))?;
			StaticTerm::Lambda(grade, bind(parameters, body))
		}
		
		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(context, term.at(expr.range), fragment)?;
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				return Err(
					ElaborationErrorKind::StaticBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(context.len()),
						expected: ty.unevaluate_in(context.len()),
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
	context: &mut Context,
	expr: Expression,
	fragment: u8,
) -> Result<(DynamicTerm, DynamicValue, StaticValue, StaticValue), ElaborationError> {
	Ok(match expr.preterm {
		// Variables.
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in context.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if let ContextType::Dynamic(ty, copy, repr) = &entry.ty {
						let result =
							(DynamicTerm::Variable(Some(name), Index(i)), ty.clone(), copy.clone(), repr.clone());
						context.take_index(i, fragment).map_err(|e| e.at(expr.range))?;
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
			let (ty, base_copy, base_repr) = elaborate_dynamic_type(context, *ty)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(&mut context.amplify(grade), *argument, fragment * (grade > 0) as u8, ty_value.clone())?;
			// TODO: Lazy evaluation.
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty, tail_copy, tail_repr) = {
				let mut context = context.extend_dynamic(
					parameters[0],
					(grade * fragment as usize).into(),
					ty_value,
					base_copy,
					base_repr,
					argument_value,
				);
				let result = synthesize_dynamic(&mut context, *tail.body, fragment)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};

			(
				DynamicTerm::Let { grade, ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) },
				tail_ty,
				tail_copy,
				tail_repr,
			)
		}

		// Splicing.
		Preterm::SwitchLevel(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, copy, repr }) = synthesize_static(context, *splicee, fragment)?
			else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*copy).clone(), (*repr).clone())
		}

		// Dependent functions.
		Preterm::Pi { grade, base, family } if fragment == 0 => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let parameters = family.parameters;
			let (family, family_copyability, family_representation) = {
				let mut context = context.bind_dynamic(
					parameters[0],
					None,
					base_value,
					base_copyability.clone(),
					base_representation.clone(),
				);
				let result = elaborate_dynamic_type(&mut context, *family.body)?;
				context.free().map_err(|e| e.at(expr.range))?;
				result
			};

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let (Ok(family_copyability), Ok(family_representation)) = (
				family_copyability.try_unevaluate_in(context.len()).into(),
				family_representation.try_unevaluate_in(context.len()).into(),
			) else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Pi {
					grade: grade.into(),
					base_copyability: base_copyability.unevaluate_in(context.len()).into(),
					base_representation: base_representation.unevaluate_in(context.len()).into(),
					base: base.into(),
					family_copyability: family_copyability.into(),
					family_representation: family_representation.into(),
					family: bind(parameters, family),
				},
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Fun)),
				},
				// TODO: Factor this out; this is common for all types.
				StaticValue::Copyability(Copyability::Trivial).into(),
				StaticValue::ReprNone.into(),
			)
		}
		Preterm::Lambda { .. } => return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),
		Preterm::Call { callee, argument } => {
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *callee, fragment)?;
			let DynamicValue::IndexedProduct {
				grade,
				base,
				family_copyability,
				family_representation,
				family,
				..
			} = scrutinee_ty
			else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument = verify_dynamic(&mut context.amplify(grade), *argument, fragment * (grade > 0) as u8, (*base).clone())?;
			let argument_value = argument.clone().evaluate_in(&context.environment);
			(
				DynamicTerm::Apply {
					scrutinee: scrutinee.into(),
					argument: argument.into(),
					fiber_copyability: family_copyability.unevaluate_in(context.len()).into(),
					fiber_representation: family_representation.unevaluate_in(context.len()).into(),
					base: base.unevaluate_in(context.len()).into(),
					family: family.unevaluate_in(context.len()),
				},
				family.evaluate_with([argument_value]),
				(*family_copyability).clone(),
				(*family_representation).clone(),
			)
		}

		// Other.
		Preterm::Former(former, arguments) => match former {
			// Types.
			Former::Universe if fragment == 0 => {
				let [copyability, representation] = arguments.try_into().unwrap();
				let copyability = verify_static(context, copyability, 0, StaticValue::CopyabilityType)?;
				let copyability_value = copyability.clone().evaluate_in(&context.environment);
				let representation = verify_static(context, representation, 0, StaticValue::ReprType)?;

				(
					DynamicTerm::Universe {
						copyability: bx!(copyability.clone()),
						representation: bx!(representation),
					},
					DynamicValue::Universe {
						copyability: StaticValue::Copyability(Copyability::Trivial).into(),
						representation: StaticValue::ReprNone.into(),
					},
					// TODO: Factor out this, this is common for all types.
					StaticValue::Copyability(Copyability::Trivial).into(),
					StaticValue::ReprNone.into(),
				)
			}

			// Repeated programs.
			Former::Exp(grade) => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, copy, repr) = elaborate_dynamic_type(context, ty)?;
				(
					DynamicTerm::Exp(grade, ty.into()),
					DynamicValue::Universe {
						copyability: copy.into(),
						representation: StaticValue::ReprExp(grade, repr.into()).into(),
					},
					StaticValue::Copyability(Copyability::Trivial).into(),
					StaticValue::ReprNone.into(),
				)
			}
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			// Repeated programs.
			Constructor::Exp(grade) => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, c, r) = synthesize_dynamic(context, tm, fragment)?;
				(
					DynamicTerm::Exp(grade, tm.into()),
					DynamicValue::Exp(grade, ty.into()),
					c,
					StaticValue::ReprExp(grade, r.into()),
				)
			}
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},

		// Synthesis failure.
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeDynamic.at(expr.range)),
	})
}

fn verify_dynamic(
	context: &mut Context,
	expr: Expression,
	fragment: u8,
	ty: DynamicValue,
) -> Result<DynamicTerm, ElaborationError> {
	Ok(match (expr.preterm, ty) {
		// Dependent functions.
		(
			Preterm::Lambda { grade, body },
			DynamicValue::IndexedProduct {
				grade: grade_t,
				base,
				base_copyability,
				base_representation,
				family,
				..
			},
		) => {
			// FIXME: Error handle
			(grade == grade_t)
				.then_some(())
				.ok_or_else(|| ElaborationErrorKind::LambdaGradeMismatch(grade, grade_t).at(expr.range))?;
			let fiber = family.autolyze(context.len());
			// TODO: Is this necessary?
			let parameters = body.parameters;
			// NOTE: Since this is the autolyzed fiber, this family has the right index but the wrong name.
			// Not sure if this is significant, as we only use indices in debugging/pretty-printing.
			// The alternatives seem to be evaluating twice (shudders) or doing find-and-replace for variables.
			// Maybe we can do the latter at some point?
			let family = bind(parameters, fiber.unevaluate_in(context.len() + 1));
			let body = {
				let mut context = context.bind_dynamic(
					parameters[0],
					(grade * fragment as usize).into(),
					base.as_ref().clone(),
					(*base_copyability).clone(),
					(*base_representation).clone(),
				);
				let body = verify_dynamic(&mut context, *body.body, fragment, fiber)?;
				context.free().map_err(|e| e.at(expr.range))?;
				body
			};

			DynamicTerm::Function {
				grade,
				base: base.unevaluate_in(context.len()).into(),
				family,
				body: bind(parameters, body),
			}
		}

		// Synthesize and conversion-check.
		(term, ty) => {
			let (term, synthesized_ty, _, _) = synthesize_dynamic(context, term.at(expr.range), fragment)?;
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				return Err(
					ElaborationErrorKind::DynamicBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(context.len()),
						expected: ty.unevaluate_in(context.len()),
					}
					.at(expr.range),
				);
			}
		}
	})
}

fn elaborate_dynamic_type(
	context: &mut Context,
	expr: Expression,
) -> Result<(DynamicTerm, /* copyability */ StaticValue, /* representation */ StaticValue), ElaborationError>
{
	let expr_range = expr.range;
	let (term, DynamicValue::Universe { copyability, representation }, _, _) =
		synthesize_dynamic(context, expr, 0)?
	else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::DynamicUniverse).at(expr_range));
	};
	Ok((term, copyability.as_ref().clone(), representation.as_ref().clone()))
}
