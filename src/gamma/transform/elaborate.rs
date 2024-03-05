use crate::{
	gamma::{
		common::{bind, Closure, Copyability, Field, Index, Level, Name, ReprAtom},
		ir::{
			domain::{Conversion, DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue, Value},
			presyntax::{Constructor, Former, Pattern, Preterm, Projector},
			syntax::{DynamicTerm, StaticTerm},
		},
		transform::{
			evaluate::{Autolyze, Evaluate, EvaluateWith},
			reify::Reify,
		},
	},
	utility::{bx, rc},
};

/// Elaborates a dynamic preterm to a dynamic term and synthesizes its type.
pub fn elaborate(term: Preterm) -> (DynamicTerm, DynamicValue) {
	let (term, ty, ..) = synthesize_dynamic(&Context::empty(), term);
	(term, ty)
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
	tys: Vec<(Name, ContextEntry)>,
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
	pub fn bind_static(mut self, name: Name, is_crisp: bool, ty: StaticValue) -> Self {
		self.environment.push(Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Static(ty))));
		self
	}

	#[must_use]
	pub fn bind_dynamic(
		mut self,
		name: Name,
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
	pub fn extend_static(mut self, name: Name, is_crisp: bool, ty: StaticValue, value: StaticValue) -> Self {
		self.environment.0.push(Value::Static(value));
		self.tys.push((name, ContextEntry::new(is_crisp, ContextType::Static(ty))));
		self
	}

	#[must_use]
	pub fn extend_dynamic(
		mut self,
		name: Name,
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

pub fn synthesize_static(context: &Context, term: Preterm) -> (StaticTerm, StaticValue) {
	match term {
		Preterm::Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, entry))| {
				if &name == name_1 {
					if context.len().0 - 1 - i >= context.lock || entry.is_crisp {
						if let ContextType::Static(ty) = &entry.ty {
							Some((StaticTerm::Variable(name, Index(i)), ty.clone()))
						} else {
							panic!("expected static variable; found dynamic variable");
						}
					} else {
						panic!("attempted to access non-crisp locked variable");
					}
				} else {
					None
				}
			})
			.unwrap(),

		Preterm::Quote(quotee) => {
			let (quotee, quotee_ty, copy, repr) = synthesize_dynamic(context, *quotee);
			(
				StaticTerm::Quote(bx!(quotee)),
				StaticValue::Lift { ty: quotee_ty.into(), copy: copy.into(), repr: repr.into() },
			)
		}

		Preterm::Let { assignee, is_crisp, ty, argument, tail } => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let ty = verify_static(arg_context.as_ref().unwrap_or(context), *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_static(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let (tail, tail_ty) = synthesize_static(
				&context.clone().extend_static(assignee, is_crisp, ty_value, argument_value),
				*tail,
			);
			(
				StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
			)
		}

		Preterm::Pi { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate_in(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, false, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Pi(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Preterm::Sigma { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate_in(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, false, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Sigma(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Preterm::Lambda { .. } | Preterm::Pair { .. } => panic!(),

		Preterm::Former(former, arguments) => match former {
			Former::Lift => {
				let [liftee] = arguments.try_into().unwrap();
				let (liftee, copy, repr) = elaborate_dynamic_type(context, liftee);
				(
					StaticTerm::Lift {
						liftee: liftee.into(),
						copy: copy.reify_in(context.len()).into(),
						repr: repr.reify_in(context.len()).into(),
					},
					StaticValue::Universe,
				)
			}
			Former::Nat if arguments.is_empty() => (StaticTerm::Nat, StaticValue::Universe),
			Former::Enum(card) if arguments.is_empty() => (StaticTerm::Enum(card), StaticValue::Universe),
			Former::Copy if arguments.is_empty() => (StaticTerm::CopyabilityType, StaticValue::Universe),
			Former::Repr if arguments.is_empty() => (StaticTerm::ReprType, StaticValue::Universe),
			Former::Universe if arguments.is_empty() => (StaticTerm::Universe, StaticValue::Universe),
			_ => panic!(),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			Constructor::Num(n) if arguments.is_empty() => (StaticTerm::Num(n), StaticValue::Nat),
			Constructor::Suc => {
				let [prev] = arguments.try_into().unwrap();
				let prev = verify_static(context, prev, StaticValue::Nat);
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
				let a = verify_static(context, a, StaticValue::CopyabilityType);
				let b = verify_static(context, b, StaticValue::CopyabilityType);
				(StaticTerm::MaxCopyability(bx!(a), bx!(b)), StaticValue::CopyabilityType)
			}
			Constructor::ReprAtom(r) if arguments.is_empty() => (StaticTerm::ReprAtom(r), StaticValue::ReprType),
			Constructor::ReprPair => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(context, r0, StaticValue::ReprType);
				let r1 = verify_static(context, r1, StaticValue::ReprType);
				(StaticTerm::ReprPair(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}
			Constructor::ReprMax => {
				let [r0, r1] = arguments.try_into().unwrap();
				let r0 = verify_static(context, r0, StaticValue::ReprType);
				let r1 = verify_static(context, r1, StaticValue::ReprType);
				(StaticTerm::ReprMax(bx!(r0), bx!(r1)), StaticValue::ReprType)
			}
			Constructor::ReprUniv => {
				let [c] = arguments.try_into().unwrap();
				let c = verify_static(context, c, StaticValue::CopyabilityType);
				(StaticTerm::ReprUniv(bx!(c)), StaticValue::ReprType)
			}
			_ => panic!(),
		},

		Preterm::Project(scrutinee, projector) => match projector {
			Projector::Field(field) => {
				let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
				let StaticValue::IndexedSum(base, family) = scrutinee_ty else { panic!() };
				match field {
					Field::Base => (StaticTerm::Project(bx!(scrutinee), field), base.as_ref().clone()),
					Field::Fiber => {
						let basepoint = StaticTerm::Project(bx!(scrutinee.clone()), Field::Base);
						let basepoint = basepoint.evaluate_in(&context.environment);
						(StaticTerm::Project(bx!(scrutinee), field), family.evaluate_with([basepoint]))
					}
				}
			}
			_ => panic!(),
		},

		Preterm::Call { callee, argument } => {
			let (callee, scrutinee_ty) = synthesize_static(context, *callee);
			let StaticValue::IndexedProduct(base, family) = scrutinee_ty else { panic!() };
			let argument = verify_static(context, *argument, (*base).clone());
			(
				StaticTerm::Apply { scrutinee: bx!(callee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&context.environment)]),
			)
		}
		Preterm::Split { scrutinee, motive_parameter, motive, cases } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			match scrutinee_ty {
				StaticValue::Nat => {
					assert!(cases.len() == 2);
					let motive = verify_static(
						&context.clone().bind_static(motive_parameter, false, StaticValue::Nat),
						*motive,
						StaticValue::Universe,
					);
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
							panic!()
						};
						let [arg] = args.try_into().unwrap();
						let Pattern::Witness { index, witness } = arg else { panic!() };
						(index, witness)
					};
					let case_suc = cases[1 - case_nil_position].1.clone();
					let case_nil =
						verify_static(context, case_nil, motive_value.evaluate_with([StaticValue::Num(0)]));
					let case_suc = verify_static(
						&context.clone().bind_static(index, false, StaticValue::Nat).bind_static(
							witness,
							false,
							motive_value.autolyze(context.len()),
						),
						case_suc,
						motive_value.evaluate_with([StaticValue::Neutral(StaticNeutral::Suc(rc!(
							StaticNeutral::Variable(index, context.len())
						)))]),
					);
					(
						StaticTerm::CaseNat {
							scrutinee: bx!(scrutinee),
							motive: bind([motive_parameter], bx!(motive)),
							case_nil: bx!(case_nil),
							case_suc: bind([index, witness], bx!(case_suc)),
						},
						motive_value.evaluate_with([scrutinee_value]),
					)
				}
				StaticValue::Enum(card) => {
					assert!(cases.len() == card as _);
					let motive_term = verify_static(
						&context.clone().bind_static(motive_parameter, false, StaticValue::Enum(card)),
						*motive,
						StaticValue::Universe,
					);
					let motive_value =
						Closure::new(context.environment.clone(), [motive_parameter], motive_term.clone());
					// TODO: Avoid cloning.
					let cases = (0..card)
						.map(|v| {
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
							verify_static(
								context,
								case,
								motive_value.evaluate_with([StaticValue::EnumValue(card, v)]),
							)
						})
						.collect();
					(
						StaticTerm::CaseEnum {
							scrutinee: bx!(scrutinee),
							motive: bind([motive_parameter], bx!(motive_term)),
							cases,
						},
						motive_value.evaluate_with([scrutinee_value]),
					)
				}
				_ => panic!(),
			}
		}
		_ => panic!(),
	}
}

pub fn verify_static(context: &Context, term: Preterm, ty: StaticValue) -> StaticTerm {
	match (term, ty) {
		(Preterm::Lambda { parameter, body }, StaticValue::IndexedProduct(base, family)) => {
			let body = verify_static(
				&context.clone().bind_static(parameter, false, base.as_ref().clone()),
				*body,
				family.autolyze(context.len()),
			);
			StaticTerm::Lambda(bind([parameter], bx!(body)))
		}
		(Preterm::Pair { basepoint, fiberpoint }, StaticValue::IndexedSum(base, family)) => {
			let basepoint = verify_static(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_static(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			StaticTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Preterm::Let { assignee, is_crisp, ty, argument, tail }, _) => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let ty = verify_static(arg_context.as_ref().unwrap_or(context), *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument =
				verify_static(arg_context.as_ref().unwrap_or(context), *argument.clone(), ty_value.clone());
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let tail = verify_static(
				&context.clone().extend_static(assignee, is_crisp, ty_value.clone(), argument_value),
				*tail,
				ty_value,
			);
			StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) }
		}
		(Preterm::Quote(quotee), StaticValue::Lift { ty: liftee, .. }) => {
			let quotee = verify_dynamic(context, *quotee, liftee);
			StaticTerm::Quote(bx!(quotee))
		}
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_static(context, term);
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				println!("{:#?}", term);
				panic!(
					"synthesized type {:#?} did not match expected type {:#?}",
					synthesized_ty.reify_in(context.len()),
					ty.reify_in(context.len()),
				);
			}
		}
	}
}

// TODO: Refactor to centralize assigning copy/repr to each type to prevent potential mistakes.
// Term, type, copyability, representation
pub fn synthesize_dynamic(
	context: &Context,
	term: Preterm,
) -> (DynamicTerm, DynamicValue, StaticValue, StaticValue) {
	match term {
		Preterm::Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, entry))| {
				if &name == name_1 {
					if context.len().0 - 1 - i >= context.lock || entry.is_crisp {
						if let ContextType::Dynamic(ty, copy, repr) = &entry.ty {
							Some((DynamicTerm::Variable(name, Index(i)), ty.clone(), copy.clone(), repr.clone()))
						} else {
							panic!("expected dynamic variable; found static variable");
						}
					} else {
						panic!("attempted to access non-crisp locked variable");
					}
				} else {
					None
				}
			})
			.unwrap(),

		Preterm::Splice(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, copy, repr }) = synthesize_static(context, *splicee)
			else {
				panic!()
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*copy).clone(), (*repr).clone())
		}

		Preterm::Let { assignee, is_crisp, ty, argument, tail } => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let (ty, base_copy, base_repr) =
				elaborate_dynamic_type(arg_context.as_ref().unwrap_or(context), *ty);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let (tail, tail_ty, tail_copy, tail_repr) = synthesize_dynamic(
				&context.clone().extend_dynamic(
					assignee,
					is_crisp,
					ty_value,
					base_copy,
					base_repr,
					argument_value,
				),
				*tail,
			);
			(
				DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
				tail_copy,
				tail_repr,
			)
		}

		Preterm::Pi { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate_in(&context.environment);
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameter,
					false,
					base_value,
					base_copyability.clone(),
					base_representation.clone(),
				),
				*family,
			);
			(
				DynamicTerm::Pi {
					base_copyability: base_copyability.reify_in(context.len()).into(),
					base_representation: base_representation.reify_in(context.len()).into(),
					base: bx!(base),
					family_copyability: family_copyability.reify_in(context.len()).into(),
					family_representation: family_representation.reify_in(context.len()).into(),
					family: bind([parameter], bx!(family)),
				},
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Fun)),
				},
				StaticValue::Copyability(Copyability::Nontrivial),
				StaticValue::ReprAtom(ReprAtom::Class),
			)
		}
		Preterm::Sigma { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate_in(&context.environment);
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameter,
					false,
					base_value,
					base_copyability.clone(),
					base_representation.clone(),
				),
				*family,
			);
			let copyability = StaticValue::max_copyability(base_copyability.clone(), family_copyability.clone());
			let representation =
				StaticValue::pair_representation(base_representation.clone(), family_representation.clone());
			(
				DynamicTerm::Sigma {
					base_copyability: base_copyability.reify_in(context.len()).into(),
					base_representation: base_representation.reify_in(context.len()).into(),
					base: bx!(base),
					family_copyability: family_copyability.reify_in(context.len()).into(),
					family_representation: family_representation.reify_in(context.len()).into(),
					family: bind([parameter], bx!(family)),
				},
				DynamicValue::Universe {
					copyability: copyability.clone().into(),
					representation: representation.clone().into(),
				},
				copyability.clone(),
				StaticValue::univ_representation(copyability),
			)
		}
		Preterm::Lambda { .. } | Preterm::Pair { .. } => panic!(),

		Preterm::Former(former, arguments) => match former {
			Former::Wrap => {
				let [ty] = arguments.try_into().unwrap();
				let (ty, copy, rep) = elaborate_dynamic_type(context, ty);
				(
					DynamicTerm::WrapType {
						inner: ty.into(),
						copyability: copy.reify_in(context.len()).into(),
						representation: rep.reify_in(context.len()).into(),
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
				let (ty, copy, repr) = elaborate_dynamic_type(context, ty);
				(
					DynamicTerm::RcType {
						inner: bx!(ty),
						copyability: copy.reify_in(context.len()).into(),
						representation: repr.reify_in(context.len()).into(),
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
			Former::Universe => {
				let [copyability, representation] = arguments.try_into().unwrap();
				let copyability = verify_static(context, copyability, StaticValue::CopyabilityType);
				let copyability_value = copyability.clone().evaluate_in(&context.environment);

				let representation = verify_static(context, representation, StaticValue::ReprType);

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
			_ => panic!(),
		},
		Preterm::Constructor(constructor, arguments) => match constructor {
			Constructor::Rc => {
				let [tm] = arguments.try_into().unwrap();
				let (tm, ty, copy, repr) = synthesize_dynamic(context, tm);
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
				let (tm, ty, copy, repr) = synthesize_dynamic(context, tm);
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
				let prev = verify_dynamic(context, prev, DynamicValue::Nat);
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
			_ => panic!(),
		},

		Preterm::Project(scrutinee, projector) => match projector {
			Projector::Rc => {
				let (tm, DynamicValue::RcType { inner: ty, copyability, representation }, _, _) =
					synthesize_dynamic(context, *scrutinee)
				else {
					panic!()
				};
				(
					DynamicTerm::UnRc {
						scrutinee: tm.into(),
						copyability: copyability.reify_in(context.len()).into(),
						representation: representation.reify_in(context.len()).into(),
					},
					ty.as_ref().clone(),
					(*copyability).clone(),
					(*representation).clone(),
				)
			}
			Projector::Wrap => {
				let (tm, DynamicValue::WrapType { inner: ty, copyability, representation }, _, _) =
					synthesize_dynamic(context, *scrutinee)
				else {
					panic!()
				};
				(
					DynamicTerm::Unwrap {
						scrutinee: bx!(tm),
						copyability: copyability.reify_in(context.len()).into(),
						representation: representation.reify_in(context.len()).into(),
					},
					ty.as_ref().clone(),
					(*copyability).clone(),
					(*representation).clone(),
				)
			}
			Projector::Field(field) => {
				let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *scrutinee);
				let DynamicValue::IndexedSum {
					base_copyability,
					base_representation,
					base,
					family_copyability,
					family_representation,
					family,
				} = scrutinee_ty
				else {
					panic!()
				};
				let basepoint = DynamicTerm::Project {
					scrutinee: scrutinee.clone().into(),
					projection: Field::Base,
					projection_copyability: base_copyability.reify_in(context.len()).into(),
					projection_representation: base_representation.reify_in(context.len()).into(),
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
								projection_copyability: family_copyability.reify_in(context.len()).into(),
								projection_representation: family_representation.reify_in(context.len()).into(),
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
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *callee);
			let DynamicValue::IndexedProduct { base, family_copyability, family_representation, family, .. } =
				scrutinee_ty
			else {
				panic!()
			};
			let argument = verify_dynamic(context, *argument, (*base).clone());
			let argument_value = argument.clone().evaluate_in(&context.environment);
			(
				DynamicTerm::Apply {
					scrutinee: bx!(scrutinee),
					argument: bx!(argument),
					fiber_copyability: family_copyability.reify_in(context.len()).into(),
					fiber_representation: family_representation.reify_in(context.len()).into(),
					base: base.reify_in(context.len()).into(),
					family: bind(
						family.parameters,
						bx!(family.autolyze(context.len()).reify_in(context.len() + 1)),
					),
				},
				family.evaluate_with([argument_value]),
				(*family_copyability).clone(),
				(*family_representation).clone(),
			)
		}
		Preterm::Split { scrutinee, motive_parameter, motive, cases } => {
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *scrutinee);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			match scrutinee_ty {
				DynamicValue::Nat => {
					assert!(cases.len() == 2);
					let (motive, fiber_copy, fiber_repr) = elaborate_dynamic_type(
						&context.clone().bind_dynamic(
							motive_parameter,
							false,
							DynamicValue::Nat,
							StaticValue::Copyability(Copyability::Nontrivial),
							StaticValue::ReprAtom(ReprAtom::Nat),
						),
						*motive,
					);
					let motive = Closure::new(context.environment.clone(), [motive_parameter], motive.clone());
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
							panic!()
						};
						let [arg] = args.try_into().unwrap();
						let Pattern::Witness { index, witness } = arg else { panic!() };
						(index, witness)
					};
					let case_suc = cases[1 - case_nil_position].1.clone();
					let case_nil = verify_dynamic(context, case_nil, motive.evaluate_with([DynamicValue::Num(0)]));
					// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
					let case_suc = verify_dynamic(
						&context
							.clone()
							.bind_dynamic(
								index,
								false,
								DynamicValue::Nat,
								StaticValue::Copyability(Copyability::Nontrivial),
								StaticValue::ReprAtom(ReprAtom::Nat),
							)
							.bind_dynamic(
								witness,
								false,
								motive.autolyze(context.len()),
								fiber_copy.clone(),
								fiber_repr.clone(),
							),
						case_suc,
						motive.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(rc!(
							DynamicNeutral::Variable(index, context.len())
						)))]),
					);
					(
						DynamicTerm::CaseNat {
							scrutinee: bx!(scrutinee),
							case_nil: bx!(case_nil),
							case_suc: bind([index, witness], bx!(case_suc)),
							fiber_copyability: fiber_copy.reify_in(context.len()).into(),
							fiber_representation: fiber_repr.reify_in(context.len()).into(),
							motive: bind(
								motive.parameters,
								bx!(motive.autolyze(context.len()).reify_in(context.len() + 1)),
							),
						},
						motive.evaluate_with([scrutinee_value]),
						fiber_copy,
						fiber_repr,
					)
				}
				DynamicValue::Enum(card) => {
					assert!(cases.len() == card as _);
					let (motive_term, fiber_copy, fiber_repr) = elaborate_dynamic_type(
						&context.clone().bind_dynamic(
							motive_parameter,
							false,
							DynamicValue::Enum(2),
							StaticValue::Copyability(Copyability::Trivial),
							StaticValue::ReprAtom(ReprAtom::Byte),
						),
						*motive,
					);
					let motive =
						Closure::new(context.environment.clone(), [motive_parameter], motive_term.clone());
					// TODO: Avoid cloning.
					let cases = (0..card)
						.map(|v| {
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
							verify_dynamic(context, case, motive.evaluate_with([DynamicValue::EnumValue(card, v)]))
						})
						.collect();
					(
						DynamicTerm::CaseEnum {
							scrutinee: bx!(scrutinee),
							cases,
							fiber_copyability: fiber_copy.reify_in(context.len()).into(),
							fiber_representation: fiber_repr.reify_in(context.len()).into(),
							motive: bind(
								motive.parameters,
								bx!(motive.autolyze(context.len()).reify_in(context.len() + 1)),
							),
						},
						motive.evaluate_with([scrutinee_value]),
						fiber_copy,
						fiber_repr,
					)
				}
				_ => panic!(),
			}
		}
		_ => panic!(),
	}
}

pub fn verify_dynamic(context: &Context, term: Preterm, ty: DynamicValue) -> DynamicTerm {
	match (term, ty) {
		(
			Preterm::Lambda { parameter, body },
			DynamicValue::IndexedProduct { base, base_copyability, base_representation, family, .. },
		) => {
			let fiber = family.autolyze(context.len());
			// TODO: Is this necessary?
			let family = bind([parameter], fiber.reify_in(context.len() + 1).into());
			let body = verify_dynamic(
				&context.clone().bind_dynamic(
					parameter,
					false,
					base.as_ref().clone(),
					(*base_copyability).clone(),
					(*base_representation).clone(),
				),
				*body,
				fiber,
			);
			DynamicTerm::Lambda {
				base: base.reify_in(context.len()).into(),
				family,
				body: bind([parameter], body.into()),
			}
		}
		(Preterm::Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_dynamic(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			DynamicTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Preterm::Let { assignee, is_crisp, ty, argument, tail }, _) => {
			let arg_context = if is_crisp { Some(context.clone().lock()) } else { None };
			let (ty, assig_copy, assig_repr) =
				elaborate_dynamic_type(arg_context.as_ref().unwrap_or(context), *ty);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(arg_context.as_ref().unwrap_or(context), *argument, ty_value.clone());
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let tail = verify_dynamic(
				&context.clone().extend_dynamic(
					assignee,
					is_crisp,
					ty_value.clone(),
					assig_copy,
					assig_repr,
					argument_value,
				),
				*tail,
				ty_value,
			);
			DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) }
		}
		(Preterm::Constructor(Constructor::Wrap, tms), DynamicValue::WrapType { inner: ty, .. }) => {
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(context, tm, ty.as_ref().clone());
			DynamicTerm::WrapNew(bx!(tm))
		}
		(Preterm::Constructor(Constructor::Rc, tms), DynamicValue::RcType { inner: ty, .. }) => {
			let [tm] = tms.try_into().unwrap();
			let tm = verify_dynamic(context, tm, ty.as_ref().clone());
			DynamicTerm::RcNew(bx!(tm))
		}
		(term, ty) => {
			let (term, synthesized_ty, _, _) = synthesize_dynamic(context, term);
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				println!("{:#?}", term);
				panic!(
					"synthesized type {:#?} did not match expected type {:#?}",
					synthesized_ty.reify_in(context.len()),
					ty.reify_in(context.len()),
				);
			}
		}
	}
}

pub fn elaborate_dynamic_type(
	context: &Context,
	term: Preterm,
) -> (DynamicTerm, /* copyability */ StaticValue, /* representation */ StaticValue) {
	let (term, DynamicValue::Universe { copyability, representation }, _, _) =
		synthesize_dynamic(context, term)
	else {
		panic!("tried to elaborate a non-type dynamic term as a type");
	};
	(term, copyability.as_ref().clone(), representation.as_ref().clone())
}
