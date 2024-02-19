use crate::{
	gamma::{
		common::{bind, Closure, Copyability, Index, Level, Name, Projection, ReprAtom},
		ir::{
			domain::{Conversion, DynamicNeutral, DynamicValue, Environment, StaticNeutral, StaticValue, Value},
			presyntax::{DynamicPreterm, StaticPreterm},
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
pub fn elaborate(term: DynamicPreterm) -> (DynamicTerm, DynamicValue) {
	let (term, ty, ..) = synthesize_dynamic(&Context::empty(), term);
	(term, ty)
}

#[derive(Clone, Debug)]
pub enum ContextType {
	Static(StaticValue),
	// Type, copyability, representation
	Dynamic(DynamicValue, StaticValue, StaticValue),
}

#[derive(Clone)]
pub struct Context {
	environment: Environment,
	tys: Vec<(Name, ContextType)>,
}

impl Context {
	pub fn empty() -> Self {
		Self { environment: Environment(Vec::new()), tys: Vec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.0.len())
	}

	#[must_use]
	pub fn bind_static(mut self, name: Name, ty: StaticValue) -> Self {
		self.environment.push(Value::Static(StaticValue::Neutral(StaticNeutral::Variable(name, self.len()))));
		self.tys.push((name, ContextType::Static(ty)));
		self
	}

	#[must_use]
	pub fn bind_dynamic(mut self, name: Name, ty: DynamicValue, copy: StaticValue, repr: StaticValue) -> Self {
		self
			.environment
			.push(Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))));
		self.tys.push((name, ContextType::Dynamic(ty, copy, repr)));
		self
	}

	#[must_use]
	pub fn extend_static(mut self, name: Name, ty: StaticValue, value: StaticValue) -> Self {
		self.environment.0.push(Value::Static(value));
		self.tys.push((name, ContextType::Static(ty)));
		self
	}

	#[must_use]
	pub fn extend_dynamic(
		mut self,
		name: Name,
		ty: DynamicValue,
		copy: StaticValue,
		repr: StaticValue,
		value: DynamicValue,
	) -> Self {
		self.environment.0.push(Value::Dynamic(value));
		self.tys.push((name, ContextType::Dynamic(ty, copy, repr)));
		self
	}
}

pub fn synthesize_static(context: &Context, term: StaticPreterm) -> (StaticTerm, StaticValue) {
	use StaticPreterm::*;
	match term {
		Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, ty))| {
				if &name == name_1 {
					if let ContextType::Static(ty) = ty {
						Some((StaticTerm::Variable(name, Index(i)), ty.clone()))
					} else {
						None
					}
				} else {
					None
				}
			})
			.unwrap(),
		CopyabilityType => (StaticTerm::CopyabilityType, StaticValue::Universe),
		Copyability(c) => (StaticTerm::Copyability(c), StaticValue::CopyabilityType),
		MaxCopyability(a, b) => {
			let a = verify_static(context, *a, StaticValue::CopyabilityType);
			let b = verify_static(context, *b, StaticValue::CopyabilityType);
			(StaticTerm::MaxCopyability(bx!(a), bx!(b)), StaticValue::CopyabilityType)
		}
		ReprType => (StaticTerm::ReprType, StaticValue::Universe),
		ReprAtom(r) => (StaticTerm::ReprAtom(r), StaticValue::ReprType),
		ReprPair(r0, r1) => {
			let r0 = verify_static(context, *r0, StaticValue::ReprType);
			let r1 = verify_static(context, *r1, StaticValue::ReprType);
			(StaticTerm::ReprPair(bx!(r0), bx!(r1)), StaticValue::ReprType)
		}
		ReprMax(r0, r1) => {
			let r0 = verify_static(context, *r0, StaticValue::ReprType);
			let r1 = verify_static(context, *r1, StaticValue::ReprType);
			(StaticTerm::ReprMax(bx!(r0), bx!(r1)), StaticValue::ReprType)
		}
		ReprUniv(c) => {
			let c = verify_static(context, *c, StaticValue::CopyabilityType);
			(StaticTerm::ReprUniv(bx!(c)), StaticValue::ReprType)
		}
		Lambda { .. } | Pair { .. } => panic!(),
		Apply { scrutinee, argument } => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
			let StaticValue::IndexedProduct(base, family) = scrutinee_ty else { panic!() };
			let argument = verify_static(context, *argument, (*base).clone());
			(
				StaticTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument.clone()) },
				family.evaluate_with([argument.evaluate_in(&context.environment)]),
			)
		}
		Project(scrutinee, projection) => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
			let StaticValue::IndexedSum(base, family) = scrutinee_ty else { panic!() };
			match projection {
				Projection::Base => (StaticTerm::Project(bx!(scrutinee), projection), base.as_ref().clone()),
				Projection::Fiber => {
					let basepoint = StaticTerm::Project(bx!(scrutinee.clone()), Projection::Base);
					let basepoint = basepoint.evaluate_in(&context.environment);
					(StaticTerm::Project(bx!(scrutinee), projection), family.evaluate_with([basepoint]))
				}
			}
		}
		Universe => (StaticTerm::Universe, StaticValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate_in(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Pi(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Sigma { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate_in(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Sigma(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Let { assignee, ty, argument, tail } => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_static(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let (tail, tail_ty) =
				synthesize_static(&context.clone().extend_static(assignee, ty_value, argument_value), *tail);
			(
				StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
			)
		}
		Lift(liftee) => {
			let (liftee, copy, repr) = elaborate_dynamic_type(context, *liftee);
			(
				StaticTerm::Lift {
					liftee: liftee.into(),
					copy: copy.reify_in(context.len()).into(),
					repr: repr.reify_in(context.len()).into(),
				},
				StaticValue::Universe,
			)
		}
		Quote(quotee) => {
			let (quotee, quotee_ty, copy, repr) = synthesize_dynamic(context, *quotee);
			(
				StaticTerm::Quote(bx!(quotee)),
				StaticValue::Lift { ty: quotee_ty.into(), copy: copy.into(), repr: repr.into() },
			)
		}

		Nat => (StaticTerm::Nat, StaticValue::Universe),
		Num(n) => (StaticTerm::Num(n), StaticValue::Nat),
		Suc(prev) => {
			let prev = verify_static(context, *prev, StaticValue::Nat);
			if let StaticTerm::Num(p) = prev {
				(StaticTerm::Num(p + 1), StaticValue::Nat)
			} else {
				(StaticTerm::Suc(bx!(prev)), StaticValue::Nat)
			}
		}
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } => {
			let scrutinee = verify_static(context, *scrutinee, StaticValue::Nat);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			let motive = verify_static(
				&context.clone().bind_static(motive_parameter, StaticValue::Nat),
				*motive,
				StaticValue::Universe,
			);
			let motive_value = Closure::new(context.environment.clone(), [motive_parameter], motive.clone());
			let case_nil = verify_static(context, *case_nil, motive_value.evaluate_with([StaticValue::Num(0)]));
			// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
			let case_suc = verify_static(
				&context.clone().bind_static(case_suc_parameters.0, StaticValue::Nat).bind_static(
					case_suc_parameters.1,
					motive_value.evaluate_with([(case_suc_parameters.0, context.len()).into()]),
				),
				*case_suc,
				motive_value.evaluate_with([StaticValue::Neutral(StaticNeutral::Suc(rc!(
					StaticNeutral::Variable(case_suc_parameters.0, context.len())
				)))]),
			);
			(
				StaticTerm::CaseNat {
					scrutinee: bx!(scrutinee),
					motive: bind([motive_parameter], bx!(motive)),
					case_nil: bx!(case_nil),
					case_suc: bind([case_suc_parameters.0, case_suc_parameters.1], bx!(case_suc)),
				},
				motive_value.evaluate_with([scrutinee_value]),
			)
		}
		Bool => (StaticTerm::Bool, StaticValue::Universe),
		BoolValue(b) => (StaticTerm::BoolValue(b), StaticValue::Bool),
		CaseBool { scrutinee, motive, case_false, case_true } => {
			let scrutinee = verify_static(context, *scrutinee, StaticValue::Bool);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			let motive_term = verify_static(
				&context.clone().bind_static(motive.parameter(), StaticValue::Bool),
				*motive.body,
				StaticValue::Universe,
			);
			let motive_value = Closure::new(context.environment.clone(), motive.parameters, motive_term.clone());
			let case_false =
				verify_static(context, *case_false, motive_value.evaluate_with([StaticValue::BoolValue(false)]));
			let case_true =
				verify_static(context, *case_true, motive_value.evaluate_with([StaticValue::BoolValue(true)]));
			(
				StaticTerm::CaseBool {
					scrutinee: bx!(scrutinee),
					motive: bind(motive.parameters, bx!(motive_term)),
					case_false: bx!(case_false),
					case_true: bx!(case_true),
				},
				motive_value.evaluate_with([scrutinee_value]),
			)
		}
	}
}

pub fn verify_static(context: &Context, term: StaticPreterm, ty: StaticValue) -> StaticTerm {
	use StaticPreterm::*;
	match (term, ty) {
		(Lambda { parameter, body }, StaticValue::IndexedProduct(base, family)) => {
			// TODO: Use Autolyze.
			let body = verify_static(
				&context.clone().bind_static(parameter, base.as_ref().clone()),
				*body,
				family.evaluate_with([(parameter, context.len()).into()]),
			);
			StaticTerm::Lambda(bind([parameter], bx!(body)))
		}
		(Pair { basepoint, fiberpoint }, StaticValue::IndexedSum(base, family)) => {
			let basepoint = verify_static(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_static(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			StaticTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_static(context, *argument.clone(), ty_value.clone());
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let tail = verify_static(
				&context.clone().extend_static(assignee, ty_value.clone(), argument_value),
				*tail,
				ty_value,
			);
			StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) }
		}
		(Quote(quotee), StaticValue::Lift { ty: liftee, .. }) => {
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
	term: DynamicPreterm,
) -> (DynamicTerm, DynamicValue, StaticValue, StaticValue) {
	use DynamicPreterm::*;
	match term {
		Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, ty))| {
				if &name == name_1 {
					if let ContextType::Dynamic(ty, copy, repr) = ty {
						Some((DynamicTerm::Variable(name, Index(i)), ty.clone(), copy.clone(), repr.clone()))
					} else {
						None
					}
				} else {
					None
				}
			})
			.unwrap(),
		Let { assignee, ty, argument, tail } => {
			let (ty, base_copy, base_repr) = elaborate_dynamic_type(context, *ty);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let (tail, tail_ty, tail_copy, tail_repr) = synthesize_dynamic(
				&context.clone().extend_dynamic(assignee, ty_value, base_copy, base_repr, argument_value),
				*tail,
			);
			(
				DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
				tail_copy,
				tail_repr,
			)
		}
		Splice(splicee) => {
			let (splicee, StaticValue::Lift { ty: liftee, copy, repr }) = synthesize_static(context, *splicee)
			else {
				panic!()
			};
			(DynamicTerm::Splice(bx!(splicee)), liftee, (*copy).clone(), (*repr).clone())
		}
		Lambda { .. } | Pair { .. } => panic!(),
		Apply { scrutinee, argument } => {
			let (scrutinee, scrutinee_ty, _, _) = synthesize_dynamic(context, *scrutinee);
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
		Project(scrutinee, projection) => {
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
				projection: Projection::Base,
				projection_copyability: base_copyability.reify_in(context.len()).into(),
				projection_representation: base_representation.reify_in(context.len()).into(),
			};
			match projection {
				Projection::Base =>
					(basepoint, base.as_ref().clone(), (*base_copyability).clone(), (*base_representation).clone()),
				Projection::Fiber => {
					let basepoint = basepoint.evaluate_in(&context.environment);
					(
						DynamicTerm::Project {
							scrutinee: scrutinee.into(),
							projection,
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
		Universe { copyability, representation } => {
			let copyability = verify_static(context, *copyability, StaticValue::CopyabilityType);
			let copyability_value = copyability.clone().evaluate_in(&context.environment);

			let representation = verify_static(context, *representation, StaticValue::ReprType);

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
		WrapType(ty) => {
			let (ty, copy, rep) = elaborate_dynamic_type(context, *ty);
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
		WrapNew(tm) => {
			let (tm, ty, copy, repr) = synthesize_dynamic(context, *tm);
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
		Unwrap(tm) => {
			let (tm, DynamicValue::WrapType { inner: ty, copyability, representation }, _, _) =
				synthesize_dynamic(context, *tm)
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
		RcType(ty) => {
			let (ty, copy, repr) = elaborate_dynamic_type(context, *ty);
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
		RcNew(tm) => {
			let (tm, ty, copy, repr) = synthesize_dynamic(context, *tm);
			(
				DynamicTerm::RcNew(bx!(tm)),
				DynamicValue::RcType { inner: ty.into(), copyability: copy.into(), representation: repr.into() },
				StaticValue::Copyability(Copyability::Nontrivial),
				StaticValue::ReprAtom(ReprAtom::Pointer),
			)
		}
		UnRc(tm) => {
			let (tm, DynamicValue::RcType { inner: ty, copyability, representation }, _, _) =
				synthesize_dynamic(context, *tm)
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
		Pi { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate_in(&context.environment);
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameter,
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
		Sigma { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate_in(&context.environment);
			let (family, family_copyability, family_representation) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					parameter,
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
		Nat => (
			DynamicTerm::Nat,
			DynamicValue::Universe {
				copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
				representation: rc!(StaticValue::ReprAtom(ReprAtom::Nat)),
			},
			StaticValue::Copyability(Copyability::Nontrivial),
			StaticValue::ReprAtom(ReprAtom::Class),
		),
		Num(n) => (
			DynamicTerm::Num(n),
			DynamicValue::Nat,
			StaticValue::Copyability(Copyability::Nontrivial),
			StaticValue::ReprAtom(ReprAtom::Nat),
		),
		Suc(prev) => {
			let prev = verify_dynamic(context, *prev, DynamicValue::Nat);
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
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } => {
			let scrutinee = verify_dynamic(context, *scrutinee, DynamicValue::Nat);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			let (motive, fiber_copy, fiber_repr) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					motive_parameter,
					DynamicValue::Nat,
					StaticValue::Copyability(Copyability::Nontrivial),
					StaticValue::ReprAtom(ReprAtom::Nat),
				),
				*motive,
			);
			let motive = Closure::new(context.environment.clone(), [motive_parameter], motive.clone());
			let case_nil = verify_dynamic(context, *case_nil, motive.evaluate_with([DynamicValue::Num(0)]));
			// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
			// TODO: Use Autolyze?
			let case_suc = verify_dynamic(
				&context
					.clone()
					.bind_dynamic(
						case_suc_parameters.0,
						DynamicValue::Nat,
						StaticValue::Copyability(Copyability::Nontrivial),
						StaticValue::ReprAtom(ReprAtom::Nat),
					)
					.bind_dynamic(
						case_suc_parameters.1,
						motive.evaluate_with([(case_suc_parameters.0, context.len()).into()]),
						fiber_copy.clone(),
						fiber_repr.clone(),
					),
				*case_suc,
				motive.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(rc!(
					DynamicNeutral::Variable(case_suc_parameters.0, context.len())
				)))]),
			);
			(
				DynamicTerm::CaseNat {
					scrutinee: bx!(scrutinee),
					case_nil: bx!(case_nil),
					case_suc: bind([case_suc_parameters.0, case_suc_parameters.1], bx!(case_suc)),
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
		Bool => (
			DynamicTerm::Bool,
			DynamicValue::Universe {
				copyability: rc!(StaticValue::Copyability(Copyability::Trivial)),
				representation: rc!(StaticValue::ReprAtom(ReprAtom::Byte)),
			},
			StaticValue::Copyability(Copyability::Trivial),
			StaticValue::ReprNone,
		),
		BoolValue(b) => (
			DynamicTerm::BoolValue(b),
			DynamicValue::Bool,
			StaticValue::Copyability(Copyability::Trivial),
			StaticValue::ReprAtom(ReprAtom::Byte),
		),
		CaseBool { scrutinee, motive, case_false, case_true } => {
			let scrutinee = verify_dynamic(context, *scrutinee, DynamicValue::Bool);
			let scrutinee_value = scrutinee.clone().evaluate_in(&context.environment);
			let (motive_term, fiber_copy, fiber_repr) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(
					motive.parameter(),
					DynamicValue::Bool,
					StaticValue::Copyability(Copyability::Trivial),
					StaticValue::ReprAtom(ReprAtom::Byte),
				),
				*motive.body,
			);
			let motive = Closure::new(context.environment.clone(), motive.parameters, motive_term.clone());
			let case_false =
				verify_dynamic(context, *case_false, motive.evaluate_with([DynamicValue::BoolValue(false)]));
			let case_true =
				verify_dynamic(context, *case_true, motive.evaluate_with([DynamicValue::BoolValue(true)]));
			(
				DynamicTerm::CaseBool {
					scrutinee: bx!(scrutinee),
					case_false: bx!(case_false),
					case_true: bx!(case_true),
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
	}
}

pub fn verify_dynamic(context: &Context, term: DynamicPreterm, ty: DynamicValue) -> DynamicTerm {
	use DynamicPreterm::*;
	match (term, ty) {
		(
			Lambda { parameter, body },
			DynamicValue::IndexedProduct { base, base_copyability, base_representation, family, .. },
		) => {
			// TODO: Use Autolyze.
			let fiber = family.evaluate_with([(parameter, context.len()).into()]);
			// TODO: Is this necessary?
			let family = bind([parameter], fiber.reify_in(context.len() + 1).into());
			let body = verify_dynamic(
				&context.clone().bind_dynamic(
					parameter,
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
		(Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate_in(&context.environment);
			let fiberpoint = verify_dynamic(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			DynamicTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let (ty, assig_copy, assig_repr) = elaborate_dynamic_type(context, *ty);
			let ty_value = ty.clone().evaluate_in(&context.environment);
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			let argument_value = argument.clone().evaluate_in(&context.environment);
			let tail = verify_dynamic(
				&context.clone().extend_dynamic(
					assignee,
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
		(WrapNew(tm), DynamicValue::WrapType { inner: ty, .. }) => {
			let tm = verify_dynamic(context, *tm, ty.as_ref().clone());
			DynamicTerm::WrapNew(bx!(tm))
		}
		(RcNew(tm), DynamicValue::RcType { inner: ty, .. }) => {
			let tm = verify_dynamic(context, *tm, ty.as_ref().clone());
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
	term: DynamicPreterm,
) -> (DynamicTerm, /* copyability */ StaticValue, /* representation */ StaticValue) {
	let (term, DynamicValue::Universe { copyability, representation }, _, _) =
		synthesize_dynamic(context, term)
	else {
		panic!("tried to elaborate a non-type dynamic term as a type");
	};
	(term, copyability.as_ref().clone(), representation.as_ref().clone())
}
