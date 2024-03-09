use crate::{
	gamma::{
		common::{bind, Binder, Closure, Copyability, Field, Index, Level, Name, ReprAtom},
		ir::{
			presyntax::{Constructor, Expression, Former, Pattern, Preterm, Projector},
			semantics::{
				Conversion, DynamicNeutral, DynamicValue, Environment, StaticNeutral,
				StaticValue, Value,
			},
			source::LexedSource,
			syntax::{DynamicTerm, StaticTerm},
		},
		transform::{
			evaluate::{Autolyze, Evaluate, EvaluateWith},
			parse::report_line_error,
			unevaluate::Unevaluate,
		},
	},
	utility::{bx, rc},
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(source: &str, lexed_source: &LexedSource, term: Expression) -> (DynamicTerm, DynamicValue) {
	match synthesize_dynamic(&Context::empty(), term) {
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
}

#[derive(Debug, Clone)]
enum ElaborationErrorKind {
	ExpectedStaticFoundDynamicVariable,
	ExpectedDynamicFoundStaticVariable,
	UsedNonCrispLockedVariable,
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
}

impl ElaborationErrorKind {
	fn at(self, range: (usize, usize)) -> ElaborationError {
		ElaborationError { range, kind: self }
	}
}

#[derive(Clone, Debug)]
pub enum ContextType {
	Static(StaticValue),
	// Type, copyability, representation
	Dynamic(DynamicValue, StaticValue, StaticValue),
}

#[derive(Clone, Debug)]
pub struct ContextEntry {
	is_crisp: bool,
	ty: ContextType,
}

impl ContextEntry {
	pub fn new(is_crisp: bool, ty: ContextType) -> Self {
		Self { is_crisp, ty }
	}
}

#[derive(Clone)]
pub struct Context {
	lock: usize,
	environment: Environment,
	tys: Vec<(Option<Name>, ContextEntry)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { lock: 0, environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.0.len())
	}

	#[must_use]
	pub fn lock(mut self) -> Self {
		self.lock = self.tys.len();
		self
	}

	#[must_use]
	pub fn bind_static(mut self, name: Option<Name>, is_crisp: bool, ty: StaticValue) -> Self {
		self.environment.push(Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Static(ty))));
		self
	}

	#[must_use]
	pub fn bind_dynamic(
		mut self,
		name: Option<Name>,
		is_crisp: bool,
		ty: DynamicValue,
		copy: StaticValue,
		repr: StaticValue,
	) -> Self {
		self
			.environment
			.push(Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Dynamic(ty, copy, repr))));
		self
	}

	#[must_use]
	pub fn extend_static(
		mut self,
		name: Option<Name>,
		is_crisp: bool,
		ty: StaticValue,
		value: StaticValue,
	) -> Self {
		self.environment.0.push(Value::Static(value));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Static(ty))));
		self
	}

	#[must_use]
	pub fn extend_dynamic(
		mut self,
		name: Option<Name>,
		is_crisp: bool,
		ty: DynamicValue,
		copy: StaticValue,
		repr: StaticValue,
		value: DynamicValue,
	) -> Self {
		self.environment.0.push(Value::Dynamic(value));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Dynamic(ty, copy, repr))));
		self
	}
}
/*
trait InferAsBoundDynType {
	type Core;
	type Telescope;
	fn infer_as_bound_dyn_type(
		&self,
		context: Context,
		telescope: Self::Telescope,
	) -> Result<Self::Core, ElaborationError>;
}

impl<const N: usize> InferAsBoundDynType for Binder<Box<Expression>, N> {
	type Core = Binder<Box<DynamicTerm>, N>;
	type Telescope = [(bool, DynamicValue); N];

	fn infer_as_bound_dyn_type(
		&self,
		context: Context,
		telescope: Self::Telescope,
	) -> Result<Self::Core, ElaborationError> {
		todo!()
	}
}
*/

fn synthesize_static(
	context: &Context,
	expr: Expression,
) -> Result<(StaticTerm, StaticValue), ElaborationError> {
	Ok(match expr.preterm {
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in context.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if context.len().0 - 1 - i >= context.lock || entry.is_crisp {
						if let ContextType::Static(ty) = &entry.ty {
							break 'var (StaticTerm::Variable(Some(name), Index(i)), ty.clone());
						} else {
							return Err(ElaborationErrorKind::ExpectedStaticFoundDynamicVariable.at(expr.range));
						}
					} else {
						return Err(ElaborationErrorKind::UsedNonCrispLockedVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		},
		Preterm::Quote(quotee) => {
			let (quotee, quotee_ty, copy, repr) = synthesize_dynamic(context, *quotee)?;
			(
				StaticTerm::Quote(bx!(quotee)),
				StaticValue::Lift { ty: quotee_ty.into(), copy: copy.into(), repr: repr.into() },
			)
		}

		Preterm::Let { is_crisp, ty, argument, tail } => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let ty = verify_static(arg_context.as_ref().unwrap_or(context), *ty, StaticValue::Universe)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_static(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone())?;
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty) = synthesize_static(
				&context.clone().extend_static(parameters[0], is_crisp, ty_value, argument_value),
				*tail.body,
			)?;
			(StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) }, tail_ty)
		}

		Preterm::Pi { base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let parameters = family.parameters;
			let family = verify_static(
				&context.clone().bind_static(parameters[0], false, base_value),
				*family.body,
				StaticValue::Universe,
			)?;
			(StaticTerm::Pi(bx!(base), bind(parameters, family)), StaticValue::Universe)
		}
		Preterm::Sigma { base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let parameters = family.parameters;
			let family = verify_static(
				&context.clone().bind_static(parameters[0], false, base_value),
				*family.body,
				StaticValue::Universe,
			)?;
			(StaticTerm::Sigma(bx!(base), bind(parameters, family)), StaticValue::Universe)
		}
		Preterm::Lambda { .. } | Preterm::Pair { .. } =>
			return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),

		Preterm::Former(former, arguments) => match former {
			Former::Lift => {
				let [liftee] = arguments.try_into().unwrap();
				let (liftee, copy, repr) = elaborate_dynamic_type(context, liftee)?;
				(
					StaticTerm::Lift {
						liftee: liftee.into(),
						copy: copy.unevaluate_in(context.len()).unwrap().into(),
						repr: repr.unevaluate_in(context.len()).unwrap().into(),
					},
					StaticValue::Universe,
				)
			}
			Former::Nat if arguments.is_empty() => (StaticTerm::Nat, StaticValue::Universe),
			Former::Enum(card) if arguments.is_empty() => (StaticTerm::Enum(card), StaticValue::Universe),
			Former::Copy if arguments.is_empty() => (StaticTerm::CopyabilityType, StaticValue::Universe),
			Former::Repr if arguments.is_empty() => (StaticTerm::ReprType, StaticValue::Universe),
			Former::Universe if arguments.is_empty() => (StaticTerm::Universe, StaticValue::Universe),
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			Constructor::Num(n) if arguments.is_empty() => (StaticTerm::Num(n), StaticValue::Nat),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_static(context, prev, StaticValue::Nat)?;
				if let StaticTerm::Num(p) = prev {
					(StaticTerm::Num(p + 1), StaticValue::Nat)
				} else {
					(StaticTerm::Suc(bx!(prev)), StaticValue::Nat)
				}
			}
			Constructor::EnumValue(k, v) if arguments.is_empty() =>
				(StaticTerm::EnumValue(k, v), StaticValue::Enum(k)),
			Constructor::Copyability(c) if arguments.is_empty() =>
				(StaticTerm::Copyability(c), StaticValue::CopyabilityType),
			Constructor::CopyMax => {
				let [a, b] = arguments.try_into().unwrap();
				let a = verify_static(context, a, StaticValue::CopyabilityType)?;
				let b = verify_static(context, b, StaticValue::CopyabilityType)?;
				(StaticTerm::MaxCopyability(bx!(a), bx!(b)), StaticValue::CopyabilityType)
			}
			Constructor::ReprAtom(r) if arguments.is_empty() => (StaticTerm::ReprAtom(r), StaticValue::ReprType),
			Constructor::ReprPair => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(context, r0, StaticValue::ReprType)?;
				let r1 = verify_static(context, r1, StaticValue::ReprType)?;
				(StaticTerm::ReprPair(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}
			Constructor::ReprMax => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(context, r0, StaticValue::ReprType)?;
				let r1 = verify_static(context, r1, StaticValue::ReprType)?;
				(StaticTerm::ReprMax(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}
			Constructor::ReprUniv => {
				let [c] = arguments.try_into().unwrap();
				let c = verify_static(context, c, StaticValue::CopyabilityType)?;
				(StaticTerm::ReprUniv(bx!(c)), StaticValue::ReprType)
			}
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},

		Preterm::Project(scrutinee, projector) => match projector {
			Projector::Field(field) => {
				let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee)?;
				let StaticValue::IndexedSum(base, family) = scrutinee_ty else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				match field {
					Field::Base => (StaticTerm::Project(bx!(scrutinee), field), base.as_ref().clone()),
					Field::Fiber => {
						let basepoint = StaticTerm::Project(bx!(scrutinee.clone()), Field::Base);
						let basepoint = basepoint.evaluate_in(&context.environment);
						(StaticTerm::Project(bx!(scrutinee), field), family.evaluate_with([basepoint]))
					}
				}
			}
			_ => return Err(ElaborationErrorKind::InvalidProjector.at(expr.range)),
		},

		Preterm::Call { callee, argument } => {
			let (callee, scrutinee_ty) = synthesize_static(context, *callee)?;
			let StaticValue::IndexedProduct(base, family) = scrutinee_ty else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument = verify_static(context, *argument, (*base).clone())?;
			(
				StaticTerm::Apply { scrutinee: bx!(callee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&context.environment)]),
			)
		}
		Preterm::Split { scrutinee, motive, cases } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee)?;
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			match scrutinee_ty {
				StaticValue::Nat => {
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == 2)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					let motive = verify_static(
						&context.clone().bind_static(motive_parameter, false, StaticValue::Nat),
						*motive.body,
						StaticValue::Universe,
					)?;
					let motive_value =
						Closure::new(context.environment.clone(), [motive_parameter], motive.clone());
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
						verify_static(context, case_nil, motive_value.evaluate_with([StaticValue::Num(0)]))?;
					let case_suc = verify_static(
						&context.clone().bind_static(Some(index), false, StaticValue::Nat).bind_static(
							Some(witness),
							false,
							motive_value.autolyze(context.len()),
						),
						case_suc,
						motive_value.evaluate_with([StaticValue::Neutral(StaticNeutral::Suc(rc!(
							StaticNeutral::Variable(Some(index), context.len())
						)))]),
					)?;
					(
						StaticTerm::CaseNat {
							scrutinee: bx!(scrutinee),
							motive: bind([motive_parameter], motive),
							case_nil: bx!(case_nil),
							case_suc: bind([Some(index), Some(witness)], case_suc),
						},
						motive_value.evaluate_with([scrutinee_value]),
					)
				}
				StaticValue::Enum(card) => {
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == card as _)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					let motive_term = verify_static(
						&context.clone().bind_static(motive_parameter, false, StaticValue::Enum(card)),
						*motive.body,
						StaticValue::Universe,
					)?;
					let motive_value =
						Closure::new(context.environment.clone(), [motive_parameter], motive_term.clone());
					// TODO: Avoid cloning.
					let mut new_cases = Vec::new();
					for v in 0..card {
						let v = v as u8;
						let case = cases[cases
							.iter()
							.position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::EnumValue(target_card, target_v), args) =
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
						new_cases.push(verify_static(
							context,
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
				_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
			}
		}
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeStatic.at(expr.range)),
	})
}

fn verify_static(
	context: &Context,
	expr: Expression,
	ty: StaticValue,
) -> Result<StaticTerm, ElaborationError> {
	Ok(match (expr.preterm, ty) {
		(Preterm::Lambda { body }, StaticValue::IndexedProduct(base, family)) => {
			let parameters = body.parameters;
			let body = verify_static(
				&context.clone().bind_static(parameters[0], false, base.as_ref().clone()),
				*body.body,
				family.autolyze(context.len()),
			)?;
			StaticTerm::Lambda(bind(parameters, body))
		}
		(Preterm::Pair { basepoint, fiberpoint }, StaticValue::IndexedSum(base, family)) => {
			let basepoint = verify_static(context, *basepoint, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_static(context, *fiberpoint, family.evaluate_with([basepoint_value]))?;
			StaticTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Preterm::Let { is_crisp, ty, argument, tail }, _) => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let ty = verify_static(arg_context.as_ref().unwrap_or(context), *ty, StaticValue::Universe)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument =
				verify_static(arg_context.as_ref().unwrap_or(context), *argument.clone(), ty_value.clone())?;
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let tail = verify_static(
				&context.clone().extend_static(parameters[0], is_crisp, ty_value.clone(), argument_value),
				*tail.body,
				ty_value,
			)?;
			StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) }
		}
		(Preterm::Quote(quotee), ty) => {
			let StaticValue::Lift { ty: liftee, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			let quotee = verify_dynamic(context, *quotee, liftee)?;
			StaticTerm::Quote(bx!(quotee))
		}
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(context, term.at(expr.range))?;
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				println!("{:#?}", term);
				// TODO: Incorporate types.
				return Err(
					ElaborationErrorKind::StaticBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(context.len()).unwrap(),
						expected: ty.unevaluate_in(context.len()).unwrap(),
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
	context: &Context,
	expr: Expression,
) -> Result<(DynamicTerm, DynamicValue, StaticValue, StaticValue), ElaborationError> {
	Ok(match expr.preterm {
		Preterm::Variable(name) => 'var: loop {
			for (i, (name_1, entry)) in context.tys.iter().rev().enumerate() {
				if &Some(name) == name_1 {
					if context.len().0 - 1 - i >= context.lock || entry.is_crisp {
						if let ContextType::Dynamic(ty, copy, repr) = &entry.ty {
							break 'var (
								DynamicTerm::Variable(Some(name), Index(i)),
								ty.clone(),
								copy.clone(),
								repr.clone(),
							);
						} else {
							return Err(ElaborationErrorKind::ExpectedDynamicFoundStaticVariable.at(expr.range));
						}
					} else {
						return Err(ElaborationErrorKind::UsedNonCrispLockedVariable.at(expr.range));
					}
				}
			}
			return Err(ElaborationErrorKind::NotInScope.at(expr.range));
		},

		Preterm::Splice(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, copy, repr }) = synthesize_static(context, *splicee)?
			else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Lift).at(expr.range));
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*copy).clone(), (*repr).clone())
		}

		Preterm::Let { is_crisp, ty, argument, tail } => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let (ty, base_copy, base_repr) =
				elaborate_dynamic_type(arg_context.as_ref().unwrap_or(context), *ty)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone())?;
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let (tail, tail_ty, tail_copy, tail_repr) = synthesize_dynamic(
				&context.clone().extend_dynamic(
					parameters[0],
					is_crisp,
					ty_value,
					base_copy,
					base_repr,
					argument_value,
				),
				*tail.body,
			)?;
			(
				DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) },
				tail_ty,
				tail_copy,
				tail_repr,
			)
		}

		Preterm::Pi { base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let parameters = family.parameters;
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameters[0],
					false,
					base_value,
					base_copyability.clone(),
					base_representation.clone(),
				),
				*family.body,
			)?;

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let (Ok(family_copyability), Ok(family_representation)) = (
				family_copyability.unevaluate_in(context.len()).into(),
				family_representation.unevaluate_in(context.len()).into(),
			) else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Pi {
					base_copyability: base_copyability.unevaluate_in(context.len()).unwrap().into(),
					base_representation: base_representation.unevaluate_in(context.len()).unwrap().into(),
					base: base.into(),
					family_copyability: family_copyability.into(),
					family_representation: family_representation.into(),
					family: bind(parameters, family),
				},
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Fun)),
				},
				StaticValue::Copyability(Copyability::Nontrivial),
				StaticValue::ReprAtom(ReprAtom::Class),
			)
		}
		Preterm::Sigma { base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base)?;
			let base_value = base.clone().evaluate_in(&context.environment);
			let parameters = family.parameters;
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameters[0],
					false,
					base_value,
					base_copyability.clone(),
					base_representation.clone(),
				),
				*family.body,
			)?;
			let copyability = StaticValue::max_copyability(base_copyability.clone(), family_copyability.clone());
			let representation =
				StaticValue::pair_representation(base_representation.clone(), family_representation.clone());

			// Ensure that the inferred fiber axes are independent of the basepoint, or error otherwise.
			let (Ok(family_copyability), Ok(family_representation)) = (
				family_copyability.unevaluate_in(context.len()).into(),
				family_representation.unevaluate_in(context.len()).into(),
			) else {
				return Err(ElaborationErrorKind::FiberAxesDependentOnBasepoint.at(expr.range));
			};

			(
				DynamicTerm::Sigma {
					base_copyability: base_copyability.unevaluate_in(context.len()).unwrap().into(),
					base_representation: base_representation.unevaluate_in(context.len()).unwrap().into(),
					base: base.into(),
					family_copyability: family_copyability.into(),
					family_representation: family_representation.into(),
					family: bind(parameters, family),
				},
				DynamicValue::Universe {
					copyability: copyability.clone().into(),
					representation: representation.clone().into(),
				},
				copyability.clone(),
				StaticValue::univ_representation(copyability),
			)
		}
		Preterm::Lambda { .. } | Preterm::Pair { .. } =>
			return Err(ElaborationErrorKind::SynthesizedLambdaOrPair.at(expr.range)),

		Preterm::Former(former, arguments) => match former {
			Former::Wrap => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, copy, rep) = elaborate_dynamic_type(context, ty)?;
				(
					DynamicTerm::WrapType {
						inner: ty.into(),
						copyability: copy.unevaluate_in(context.len()).unwrap().into(),
						representation: rep.unevaluate_in(context.len()).unwrap().into(),
					},
					DynamicValue::Universe {
						copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial).clone()),
						representation: rc!(rep.clone()),
					},
					StaticValue::Copyability(Copyability::Nontrivial),
					StaticValue::ReprAtom(ReprAtom::Class),
				)
			}
			Former::Rc => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, copy, repr) = elaborate_dynamic_type(context, ty)?;
				(
					DynamicTerm::RcType {
						inner: ty.into(),
						copyability: copy.unevaluate_in(context.len()).unwrap().into(),
						representation: repr.unevaluate_in(context.len()).unwrap().into(),
					},
					DynamicValue::Universe {
						copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
						representation: rc!(StaticValue::ReprAtom(ReprAtom::Pointer)),
					},
					StaticValue::Copyability(Copyability::Nontrivial),
					StaticValue::ReprAtom(ReprAtom::Class),
				)
			}
			Former::Nat if arguments.is_empty() => (
				DynamicTerm::Nat,
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Nat)),
				},
				StaticValue::Copyability(Copyability::Nontrivial),
				StaticValue::ReprAtom(ReprAtom::Class),
			),
			// TODO: Optimize if subsingleton.
			Former::Enum(card) if arguments.is_empty() => (
				DynamicTerm::Enum(card),
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Trivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Byte)),
				},
				StaticValue::Copyability(Copyability::Trivial),
				StaticValue::ReprNone,
			),
			Former::Id => {
				let [ty, x, y] = arguments.try_into().unwrap();
				let (ty, copy, repr) = elaborate_dynamic_type(context, ty)?;
				let ty_value = ty.clone().evaluate_in(&context.environment);
				let x = verify_dynamic(context, x, ty_value.clone())?;
				let y = verify_dynamic(context, y, ty_value.clone())?;
				(
					DynamicTerm::Id {
						copy: copy.unevaluate_in(context.len()).unwrap().into(),
						repr: repr.unevaluate_in(context.len()).unwrap().into(),
						space: ty.into(),
						left: x.into(),
						right: y.into(),
					},
					DynamicValue::Universe {
						copyability: rc!(StaticValue::Copyability(Copyability::Trivial)),
						representation: rc!(StaticValue::ReprNone),
					},
					StaticValue::Copyability(Copyability::Trivial),
					StaticValue::ReprNone,
				)
			}
			Former::Universe => {
				let [copyability, representation] = arguments.try_into().unwrap();
				let copyability = verify_static(context, copyability, StaticValue::CopyabilityType)?;
				let copyability_value = copyability.clone().evaluate_in(&context.environment);

				let representation = verify_static(context, representation, StaticValue::ReprType)?;

				let universe_representation = StaticValue::univ_representation(copyability_value.clone());

				(
					DynamicTerm::Universe {
						copyability: bx!(copyability.clone()),
						representation: bx!(representation),
					},
					DynamicValue::Universe {
						copyability: rc!(copyability_value.clone()),
						representation: rc!(universe_representation.clone()),
					},
					copyability_value,
					universe_representation,
				)
			}
			_ => return Err(ElaborationErrorKind::InvalidFormer.at(expr.range)),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			Constructor::Rc => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, copy, repr) = synthesize_dynamic(context, tm)?;
				(
					DynamicTerm::RcNew(bx!(tm)),
					DynamicValue::RcType {
						inner: ty.into(),
						copyability: copy.into(),
						representation: repr.into(),
					},
					StaticValue::Copyability(Copyability::Nontrivial),
					StaticValue::ReprAtom(ReprAtom::Pointer),
				)
			}
			Constructor::Wrap => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, copy, repr) = synthesize_dynamic(context, tm)?;
				(
					DynamicTerm::WrapNew(bx!(tm)),
					DynamicValue::WrapType {
						inner: ty.into(),
						copyability: copy.into(),
						representation: repr.clone().into(),
					},
					StaticValue::Copyability(Copyability::Nontrivial),
					repr,
				)
			}
			Constructor::Num(n) if arguments.is_empty() => (
				DynamicTerm::Num(n),
				DynamicValue::Nat,
				StaticValue::Copyability(Copyability::Nontrivial),
				StaticValue::ReprAtom(ReprAtom::Nat),
			),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_dynamic(context, prev, DynamicValue::Nat)?;
				if let DynamicTerm::Num(p) = prev {
					(
						DynamicTerm::Num(p + 1),
						DynamicValue::Nat,
						StaticValue::Copyability(Copyability::Nontrivial),
						StaticValue::ReprAtom(ReprAtom::Nat),
					)
				} else {
					(
						DynamicTerm::Suc(bx!(prev)),
						DynamicValue::Nat,
						StaticValue::Copyability(Copyability::Nontrivial),
						StaticValue::ReprAtom(ReprAtom::Nat),
					)
				}
			}
			Constructor::EnumValue(k, v) if arguments.is_empty() => (
				DynamicTerm::EnumValue(k, v),
				DynamicValue::Enum(k),
				StaticValue::Copyability(Copyability::Trivial),
				StaticValue::ReprAtom(ReprAtom::Byte),
			),
			Constructor::Refl => {
				let [x] = arguments.try_into().unwrap();
				let (x, ty_value, copy, repr) = synthesize_dynamic(context, x)?;

				let ty = ty_value.unevaluate_in(context.len()).unwrap();
				let x_value = x.clone().evaluate_in(&context.environment);
				(
					DynamicTerm::Refl(ty.into(), x.into()),
					DynamicValue::Id {
						copy: copy.into(),
						repr: repr.into(),
						space: ty_value.into(),
						left: x_value.clone().into(),
						right: x_value.into(),
					},
					StaticValue::Copyability(Copyability::Trivial),
					StaticValue::ReprNone,
				)
			}
			_ => return Err(ElaborationErrorKind::InvalidConstructor.at(expr.range)),
		},

		Preterm::Project(scrutinee, projector) => match projector {
			Projector::Rc => {
				let (tm, DynamicValue::RcType { inner: ty, copyability, representation }, _, _) =
					synthesize_dynamic(context, *scrutinee)?
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Rc).at(expr.range));
				};
				(
					DynamicTerm::UnRc {
						scrutinee: tm.into(),
						copyability: copyability.unevaluate_in(context.len()).unwrap().into(),
						representation: representation.unevaluate_in(context.len()).unwrap().into(),
					},
					ty.as_ref().clone(),
					(*copyability).clone(),
					(*representation).clone(),
				)
			}
			Projector::Wrap => {
				let (tm, DynamicValue::WrapType { inner: ty, copyability, representation }, _, _) =
					synthesize_dynamic(context, *scrutinee)?
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Wrap).at(expr.range));
				};
				(
					DynamicTerm::Unwrap {
						scrutinee: bx!(tm),
						copyability: copyability.unevaluate_in(context.len()).unwrap().into(),
						representation: representation.unevaluate_in(context.len()).unwrap().into(),
					},
					ty.as_ref().clone(),
					(*copyability).clone(),
					(*representation).clone(),
				)
			}
			Projector::Field(field) => {
				let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *scrutinee)?;
				let DynamicValue::IndexedSum {
					base_copyability,
					base_representation,
					base,
					family_copyability,
					family_representation,
					family,
				} = scrutinee_ty
				else {
					return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Sigma).at(expr.range));
				};
				let basepoint = DynamicTerm::Project {
					scrutinee: scrutinee.clone().into(),
					projection: Field::Base,
					projection_copyability: base_copyability.unevaluate_in(context.len()).unwrap().into(),
					projection_representation: base_representation.unevaluate_in(context.len()).unwrap().into(),
				};
				match field {
					Field::Base => (
						basepoint,
						base.as_ref().clone(),
						(*base_copyability).clone(),
						(*base_representation).clone(),
					),
					Field::Fiber => {
						let basepoint = basepoint.evaluate_in(&context.environment);
						(
							DynamicTerm::Project {
								scrutinee: scrutinee.into(),
								projection: field,
								projection_copyability: family_copyability
									.unevaluate_in(context.len())
									.unwrap()
									.into(),
								projection_representation: family_representation
									.unevaluate_in(context.len())
									.unwrap()
									.into(),
							},
							family.evaluate_with([basepoint]),
							(*family_copyability).clone(),
							(*family_representation).clone(),
						)
					}
				}
			}
		},
		Preterm::Call { callee, argument } => {
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *callee)?;
			let DynamicValue::IndexedProduct { base, family_copyability, family_representation, family, .. } =
				scrutinee_ty
			else {
				return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::Pi).at(expr.range));
			};
			let argument = verify_dynamic(context, *argument, (*base).clone())?;
			let argument_value = argument.clone().evaluate_in(&context.environment);
			(
				DynamicTerm::Apply {
					scrutinee: scrutinee.into(),
					argument: argument.into(),
					fiber_copyability: family_copyability.unevaluate_in(context.len()).unwrap().into(),
					fiber_representation: family_representation.unevaluate_in(context.len()).unwrap().into(),
					base: base.unevaluate_in(context.len()).unwrap().into(),
					family: family.unevaluate_in(context.len()).unwrap(),
				},
				family.evaluate_with([argument_value]),
				(*family_copyability).clone(),
				(*family_representation).clone(),
			)
		}
		Preterm::Split { scrutinee, motive, cases } => {
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *scrutinee)?;
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			match scrutinee_ty {
				DynamicValue::Nat => {
					// TODO: Handle this error.
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == 2)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					// TODO: Throw specific error if copy/repr depend on the motive.
					let (motive_term, fiber_copy, fiber_repr) = elaborate_dynamic_type(
						&context.clone().bind_dynamic(
							motive_parameter,
							false,
							DynamicValue::Nat,
							StaticValue::Copyability(Copyability::Nontrivial),
							StaticValue::ReprAtom(ReprAtom::Nat),
						),
						*motive.body,
					)?;
					let motive =
						Closure::new(context.environment.clone(), [motive_parameter], motive_term.clone());
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
						verify_dynamic(context, case_nil, motive.evaluate_with([DynamicValue::Num(0)]))?;
					// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
					let case_suc = verify_dynamic(
						&context
							.clone()
							.bind_dynamic(
								Some(index),
								false,
								DynamicValue::Nat,
								StaticValue::Copyability(Copyability::Nontrivial),
								StaticValue::ReprAtom(ReprAtom::Nat),
							)
							.bind_dynamic(
								Some(witness),
								false,
								motive.autolyze(context.len()),
								fiber_copy.clone(),
								fiber_repr.clone(),
							),
						case_suc,
						motive.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(rc!(
							DynamicNeutral::Variable(Some(index), context.len())
						)))]),
					)?;
					(
						DynamicTerm::CaseNat {
							scrutinee: bx!(scrutinee),
							case_nil: bx!(case_nil),
							case_suc: bind([Some(index), Some(witness)], case_suc),
							fiber_copyability: fiber_copy.unevaluate_in(context.len()).unwrap().into(),
							fiber_representation: fiber_repr.unevaluate_in(context.len()).unwrap().into(),
							motive: bind([motive_parameter], motive_term),
						},
						motive.evaluate_with([scrutinee_value]),
						fiber_copy,
						fiber_repr,
					)
				}
				DynamicValue::Enum(card) => {
					// TODO: Handle this error.
					let [motive_parameter] = (*motive.parameters).try_into().unwrap();
					(cases.len() == card as _)
						.then_some(())
						.ok_or(ElaborationErrorKind::InvalidCaseSplit.at(expr.range))?;
					// TODO: Throw specific error if copy/repr depend on the motive.
					let (motive_term, fiber_copy, fiber_repr) = elaborate_dynamic_type(
						&context.clone().bind_dynamic(
							motive_parameter,
							false,
							DynamicValue::Enum(2),
							StaticValue::Copyability(Copyability::Trivial),
							StaticValue::ReprAtom(ReprAtom::Byte),
						),
						*motive.body,
					)?;
					let motive =
						Closure::new(context.environment.clone(), [motive_parameter], motive_term.clone());
					// TODO: Avoid cloning.
					let mut new_cases = Vec::new();
					for v in 0..card {
						let v = v as u8;
						let case = cases[cases
							.iter()
							.position(|(pattern, _)| {
								if let Pattern::Construction(Constructor::EnumValue(target_card, target_v), args) =
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
							context,
							case,
							motive.evaluate_with([DynamicValue::EnumValue(card, v)]),
						)?)
					}
					(
						DynamicTerm::CaseEnum {
							scrutinee: bx!(scrutinee),
							cases: new_cases,
							fiber_copyability: fiber_copy.unevaluate_in(context.len()).unwrap().into(),
							fiber_representation: fiber_repr.unevaluate_in(context.len()).unwrap().into(),
							motive: bind([motive_parameter], motive_term),
						},
						motive.evaluate_with([scrutinee_value]),
						fiber_copy,
						fiber_repr,
					)
				}
				DynamicValue::Id { copy, repr, space, left, right } => {
					// TODO: Something more like:
					// let motive = elaborate_dynamic_motive([space, space, id(space, var(1), var(0))]);

					// TODO: Handle this error.
					let [u, v, p] = (*motive.parameters).try_into().unwrap();
					let Ok([(Pattern::Construction(Constructor::Refl, pattern), case_refl)]) =
						<[_; 1]>::try_from(cases)
					else {
						return Err(ElaborationErrorKind::InvalidCaseSplit.at(expr.range));
					};
					let Ok([Pattern::Variable(refl_pattern_endpoint)]) = <[_; 1]>::try_from(pattern) else {
						panic!();
					};

					// TODO: Throw specific error if copy/repr depend on the motive.
					let (motive_term, fiber_copy, fiber_repr) = elaborate_dynamic_type(
						&context
							.clone()
							.bind_dynamic(u, false, (*space).clone(), (*copy).clone(), (*repr).clone())
							.bind_dynamic(v, false, (*space).clone(), (*copy).clone(), (*repr).clone())
							.bind_dynamic(
								p,
								false,
								DynamicValue::Id {
									copy: copy.clone(),
									repr: repr.clone(),
									space: space.clone(),
									left: DynamicValue::Neutral(DynamicNeutral::Variable(u, context.len())).into(),
									right: DynamicValue::Neutral(DynamicNeutral::Variable(v, context.len() + 1))
										.into(),
								},
								StaticValue::Copyability(Copyability::Trivial), // Copyability for paths
								StaticValue::ReprNone,                          // Representation for Paths
							),
						*motive.body,
					)?;
					let motive = Closure::new(context.environment.clone(), [u, v, p], motive_term.clone());

					let refl_pattern_endpoint_variable =
						DynamicValue::Neutral(DynamicNeutral::Variable(Some(refl_pattern_endpoint), context.len()));
					let case_refl = verify_dynamic(
						&context.clone().bind_dynamic(
							Some(refl_pattern_endpoint),
							false,
							(*space).clone(),
							(*copy).clone(),
							(*repr).clone(),
						),
						case_refl,
						motive.evaluate_with([
							refl_pattern_endpoint_variable.clone(),
							refl_pattern_endpoint_variable.clone(),
							DynamicValue::Refl(space, refl_pattern_endpoint_variable.into()),
						]),
					)?;

					(
						DynamicTerm::CasePath {
							scrutinee: scrutinee.into(),
							motive: bind([u, v, p], motive_term),
							case_refl: bind([Some(refl_pattern_endpoint)], case_refl),
						},
						motive.evaluate_with([(*left).clone(), (*right).clone(), scrutinee_value]),
						fiber_copy,
						fiber_repr,
					)
				}
				_ => return Err(ElaborationErrorKind::InvalidCaseSplitScrutineeType.at(expr.range)),
			}
		}
		_ => return Err(ElaborationErrorKind::CouldNotSynthesizeDynamic.at(expr.range)),
	})
}

fn verify_dynamic(
	context: &Context,
	expr: Expression,
	ty: DynamicValue,
) -> Result<DynamicTerm, ElaborationError> {
	Ok(match (expr.preterm, ty) {
		(
			Preterm::Lambda { body },
			DynamicValue::IndexedProduct { base, base_copyability, base_representation, family, .. },
		) => {
			let fiber = family.autolyze(context.len());
			// TODO: Is this necessary?
			let parameters = body.parameters;
			let family = bind(parameters, fiber.unevaluate_in(context.len() + 1).unwrap());
			let body = verify_dynamic(
				&context.clone().bind_dynamic(
					parameters[0],
					false,
					base.as_ref().clone(),
					(*base_copyability).clone(),
					(*base_representation).clone(),
				),
				*body.body,
				fiber,
			)?;
			DynamicTerm::Lambda {
				base: base.unevaluate_in(context.len()).unwrap().into(),
				family,
				body: bind(parameters, body),
			}
		}
		(Preterm::Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(context, *basepoint, base.as_ref().clone())?;
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_dynamic(context, *fiberpoint, family.evaluate_with([basepoint_value]))?;
			DynamicTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Preterm::Let { is_crisp, ty, argument, tail }, _) => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let (ty, assig_copy, assig_repr) =
				elaborate_dynamic_type(arg_context.as_ref().unwrap_or(context), *ty)?;
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone())?;
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let parameters = tail.parameters;
			let tail = verify_dynamic(
				&context.clone().extend_dynamic(
					parameters[0],
					is_crisp,
					ty_value.clone(),
					assig_copy,
					assig_repr,
					argument_value,
				),
				*tail.body,
				ty_value,
			)?;
			DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind(parameters, tail) }
		}
		(Preterm::Constructor(Constructor::Wrap, tms), ty) => {
			let DynamicValue::WrapType { inner: ty, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Wrap).at(expr.range));
			};
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(context, tm, ty.as_ref().clone())?;
			DynamicTerm::WrapNew(bx!(tm))
		}
		(Preterm::Constructor(Constructor::Rc, tms), ty) => {
			let DynamicValue::RcType { inner: ty, .. } = ty else {
				return Err(ElaborationErrorKind::SynthesizedFormer(ExpectedFormer::Rc).at(expr.range));
			};
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(context, tm, ty.as_ref().clone())?;
			DynamicTerm::RcNew(bx!(tm))
		}
		(term, ty) => {
			let (term, synthesized_ty, _, _) = synthesize_dynamic(context, term.at(expr.range))?;
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				return Err(
					ElaborationErrorKind::DynamicBidirectionalMismatch {
						synthesized: synthesized_ty.unevaluate_in(context.len()).unwrap(),
						expected: ty.unevaluate_in(context.len()).unwrap(),
					}
					.at(expr.range),
				);
			}
		}
	})
}

fn elaborate_dynamic_type(
	context: &Context,
	expr: Expression,
) -> Result<(DynamicTerm, /* copyability */ StaticValue, /* representation */ StaticValue), ElaborationError>
{
	let expr_range = expr.range;
	let (term, DynamicValue::Universe { copyability, representation }, _, _) =
		synthesize_dynamic(context, expr)?
	else {
		return Err(ElaborationErrorKind::ExpectedFormer(ExpectedFormer::DynamicUniverse).at(expr_range));
	};
	Ok((term, copyability.as_ref().clone(), representation.as_ref().clone()))
}
