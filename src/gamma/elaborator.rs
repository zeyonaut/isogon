use super::{
	common::{bind, Binder, Copyability, Index, Level, Name, Projection, ReprAtom},
	conversion::Conversion,
	evaluator::{
		DynamicNeutral, DynamicValue, Environment, Evaluate, Reify, StaticNeutral, StaticValue, Value,
	},
	parser::{DynamicPreterm, StaticPreterm},
};
use crate::{
	gamma::{common::Closure, evaluator::EvaluateWith},
	utility::{bx, rc},
};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Name, Index),
	Let {
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
	Universe,
	Pi(Box<Self>, Binder<Box<Self>>),
	Lambda(Binder<Box<Self>>),
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma(Box<Self>, Binder<Box<Self>>),
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
	CopyabilityType,
	Copyability(Copyability),
	MaxCopyability(Box<Self>, Box<Self>),
	ReprType,
	ReprAtom(Option<ReprAtom>),
	ReprPair(Box<Self>, Box<Self>),
	ReprMax(Box<Self>, Box<Self>),
	ReprUniv(Box<Self>),
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Name, Index),
	Let {
		// Type of the assignee.
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Splice(Box<StaticTerm>),
	Universe {
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
	WrapType(Box<Self>),
	WrapNew(Box<Self>),
	Unwrap(Box<Self>),
	RcType(Box<Self>),
	RcNew(Box<Self>),
	UnRc(Box<Self>),
	Pi {
		base_copyability: StaticValue,
		base_representation: StaticValue,
		base: Box<Self>,
		family_copyability: StaticValue,
		family_representation: StaticValue,
		family: Binder<Box<Self>>,
	},
	Lambda {
		base: Box<Self>,
		family: Binder<Box<Self>>,
		body: Binder<Box<Self>>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		base_copyability: StaticValue,
		base_representation: StaticValue,
		base: Box<Self>,
		family_copyability: StaticValue,
		family_representation: StaticValue,
		family: Binder<Box<Self>>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
}

#[derive(Clone)]
pub struct Context {
	environment: Environment,
	tys: Vec<(Name, Value)>,
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
		self.tys.push((name, Value::Static(ty)));
		self
	}

	#[must_use]
	pub fn bind_dynamic(mut self, name: Name, ty: DynamicValue) -> Self {
		self
			.environment
			.push(Value::Dynamic(DynamicValue::Neutral(DynamicNeutral::Variable(name, self.len()))));
		self.tys.push((name, Value::Dynamic(ty)));
		self
	}

	#[must_use]
	pub fn extend(mut self, name: Name, ty: Value, value: Value) -> Self {
		self.environment.0.push(value);
		self.tys.push((name, ty));
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
					if let Value::Static(ty) = ty {
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
				family.evaluate_with([argument.evaluate(&context.environment)]),
			)
		}
		Project(scrutinee, projection) => {
			let (scrutinee, scrutinee_ty) = synthesize_static(context, *scrutinee);
			let StaticValue::IndexedSum(base, family) = scrutinee_ty else { panic!() };
			match projection {
				Projection::Base => (StaticTerm::Project(bx!(scrutinee), projection), base.as_ref().clone()),
				Projection::Fiber => {
					let basepoint = StaticTerm::Project(bx!(scrutinee.clone()), Projection::Base);
					let basepoint = basepoint.evaluate(&context.environment);
					(StaticTerm::Project(bx!(scrutinee), projection), family.evaluate_with([basepoint]))
				}
			}
		}
		Universe => (StaticTerm::Universe, StaticValue::Universe),
		Pi { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Pi(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Sigma { parameter, base, family } => {
			let base = verify_static(context, *base, StaticValue::Universe);
			let base_value = base.clone().evaluate(&context.environment);
			let family = verify_static(
				&context.clone().bind_static(parameter, base_value),
				*family,
				StaticValue::Universe,
			);
			(StaticTerm::Sigma(bx!(base), bind([parameter], bx!(family))), StaticValue::Universe)
		}
		Let { assignee, ty, argument, tail } => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate(&context.environment);
			let argument = verify_static(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate(&context.environment);
			let (tail, tail_ty) = synthesize_static(
				&context.clone().extend(assignee, Value::Static(ty_value), Value::Static(argument_value)),
				*tail,
			);
			(
				StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
			)
		}
		Lift(liftee) => {
			let (liftee, _, _) = elaborate_dynamic_type(context, *liftee);
			(StaticTerm::Lift(bx!(liftee)), StaticValue::Universe)
		}
		Quote(quotee) => {
			let (quotee, quotee_ty) = synthesize_dynamic(context, *quotee);
			(StaticTerm::Quote(bx!(quotee)), StaticValue::Lift(quotee_ty.into()))
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
			let scrutinee_value = scrutinee.clone().evaluate(&context.environment);
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
			let scrutinee_value = scrutinee.clone().evaluate(&context.environment);
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
			let body = verify_static(
				&context.clone().bind_static(parameter, base.as_ref().clone()),
				*body,
				family.evaluate_with([(parameter, context.len()).into()]),
			);
			StaticTerm::Lambda(bind([parameter], bx!(body)))
		}
		(Pair { basepoint, fiberpoint }, StaticValue::IndexedSum(base, family)) => {
			let basepoint = verify_static(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate(&context.environment);
			let fiberpoint = verify_static(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			StaticTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let ty = verify_static(context, *ty, StaticValue::Universe);
			let ty_value = ty.clone().evaluate(&context.environment);
			let argument = verify_static(context, *argument.clone(), ty_value.clone());
			let argument_value = argument.clone().evaluate(&context.environment);
			let tail = verify_static(
				&context.clone().extend(assignee, Value::Static(ty_value.clone()), Value::Static(argument_value)),
				*tail,
				ty_value,
			);
			StaticTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) }
		}
		(Quote(quotee), StaticValue::Lift(liftee)) => {
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
					synthesized_ty.reify(context.len()),
					ty.reify(context.len()),
				);
			}
		}
	}
}

pub fn elaborate_dynamic_closed(term: DynamicPreterm) -> (DynamicTerm, DynamicValue) {
	synthesize_dynamic(&Context::empty(), term)
}

pub fn synthesize_dynamic(context: &Context, term: DynamicPreterm) -> (DynamicTerm, DynamicValue) {
	use DynamicPreterm::*;
	match term {
		Variable(name) => context
			.tys
			.iter()
			.rev()
			.enumerate()
			.find_map(|(i, (name_1, ty))| {
				if &name == name_1 {
					if let Value::Dynamic(ty) = ty {
						Some((DynamicTerm::Variable(name, Index(i)), ty.clone()))
					} else {
						None
					}
				} else {
					None
				}
			})
			.unwrap(),
		Let { assignee, ty, argument, tail } => {
			let (ty, _, _) = elaborate_dynamic_type(context, *ty);
			let ty_value = ty.clone().evaluate(&context.environment);
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			// NOTE: Isn't this a problem, performance-wise? Does laziness help here? Testing necessary. (Having the value available in the environment is wanted for evaluation.)
			let argument_value = argument.clone().evaluate(&context.environment);
			let (tail, tail_ty) = synthesize_dynamic(
				&context.clone().extend(assignee, Value::Dynamic(ty_value), Value::Dynamic(argument_value)),
				*tail,
			);
			(
				DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) },
				tail_ty,
			)
		}
		Splice(splicee) => {
			let (splicee, StaticValue::Lift(liftee)) = synthesize_static(context, *splicee) else { panic!() };
			(DynamicTerm::Splice(bx!(splicee)), liftee)
		}
		Lambda { .. } | Pair { .. } => panic!(),
		Apply { scrutinee, argument } => {
			let (scrutinee, scrutinee_ty) = synthesize_dynamic(context, *scrutinee);
			let DynamicValue::IndexedProduct { base, family, .. } = scrutinee_ty else { panic!() };
			let argument = verify_dynamic(context, *argument, (*base).clone());
			let argument_value = argument.clone().evaluate(&context.environment);
			(
				DynamicTerm::Apply { scrutinee: bx!(scrutinee), argument: bx!(argument) },
				family.evaluate_with([argument_value]),
			)
		}
		Project(scrutinee, projection) => {
			let (scrutinee, scrutinee_ty) = synthesize_dynamic(context, *scrutinee);
			let DynamicValue::IndexedSum { base, family, .. } = scrutinee_ty else { panic!() };
			match projection {
				Projection::Base => (DynamicTerm::Project(bx!(scrutinee), projection), base.as_ref().clone()),
				Projection::Fiber => {
					let basepoint = DynamicTerm::Project(bx!(scrutinee.clone()), Projection::Base);
					let basepoint = basepoint.evaluate(&context.environment);
					(DynamicTerm::Project(bx!(scrutinee), projection), family.evaluate_with([basepoint]))
				}
			}
		}
		Universe { copyability, representation } => {
			let copyability = verify_static(context, *copyability, StaticValue::CopyabilityType);
			let copyability_value = copyability.clone().evaluate(&context.environment);

			let representation = verify_static(context, *representation, StaticValue::ReprType);

			let universe_representation = StaticValue::univ_representation(copyability_value.clone());

			(
				DynamicTerm::Universe {
					copyability: bx!(copyability.clone()),
					representation: bx!(representation),
				},
				DynamicValue::Universe {
					copyability: rc!(copyability_value),
					representation: rc!(universe_representation),
				},
			)
		}
		WrapType(ty) => {
			let (ty, _, rep) = elaborate_dynamic_type(context, *ty);
			(
				DynamicTerm::WrapType(bx!(ty)),
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(rep),
				},
			)
		}
		WrapNew(tm) => {
			let (tm, ty) = synthesize_dynamic(context, *tm);
			(DynamicTerm::WrapNew(bx!(tm)), DynamicValue::WrapType(rc!(ty)))
		}
		Unwrap(tm) => {
			let (tm, DynamicValue::WrapType(ty)) = synthesize_dynamic(context, *tm) else { panic!() };
			(DynamicTerm::Unwrap(bx!(tm)), ty.as_ref().clone())
		}
		RcType(ty) => {
			let (ty, _, _) = elaborate_dynamic_type(context, *ty);
			(
				DynamicTerm::RcType(bx!(ty)),
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Pointer)),
				},
			)
		}
		RcNew(tm) => {
			let (tm, ty) = synthesize_dynamic(context, *tm);
			(DynamicTerm::RcNew(bx!(tm)), DynamicValue::RcType(rc!(ty)))
		}
		UnRc(tm) => {
			let (tm, DynamicValue::RcType(ty)) = synthesize_dynamic(context, *tm) else { panic!() };
			(DynamicTerm::UnRc(bx!(tm)), ty.as_ref().clone())
		}
		Pi { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate(&context.environment);
			let (family, family_copyability, family_representation) =
				elaborate_dynamic_type(&context.clone().bind_dynamic(parameter, base_value), *family);
			(
				DynamicTerm::Pi {
					base_copyability,
					base_representation,
					base: bx!(base),
					family_copyability,
					family_representation,
					family: bind([parameter], bx!(family)),
				},
				DynamicValue::Universe {
					copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
					representation: rc!(StaticValue::ReprAtom(ReprAtom::Fun)),
				},
			)
		}
		Sigma { parameter, base, family } => {
			let (base, base_copyability, base_representation) = elaborate_dynamic_type(context, *base);
			let base_value = base.clone().evaluate(&context.environment);
			let (family, family_copyability, family_representation) =
				elaborate_dynamic_type(&context.clone().bind_dynamic(parameter, base_value), *family);
			let copyability = StaticValue::max_copyability(base_copyability.clone(), family_copyability.clone());
			let representation =
				StaticValue::pair_representation(base_representation.clone(), family_representation.clone());
			(
				DynamicTerm::Sigma {
					base_copyability,
					base_representation,
					base: bx!(base),
					family_copyability,
					family_representation,
					family: bind([parameter], bx!(family)),
				},
				DynamicValue::Universe { copyability: rc!(copyability), representation: rc!(representation) },
			)
		}
		Nat => (
			DynamicTerm::Nat,
			DynamicValue::Universe {
				copyability: rc!(StaticValue::Copyability(Copyability::Nontrivial)),
				representation: rc!(StaticValue::ReprAtom(ReprAtom::Nat)),
			},
		),
		Num(n) => (DynamicTerm::Num(n), DynamicValue::Nat),
		Suc(prev) => {
			let prev = verify_dynamic(context, *prev, DynamicValue::Nat);
			if let DynamicTerm::Num(p) = prev {
				(DynamicTerm::Num(p + 1), DynamicValue::Nat)
			} else {
				(DynamicTerm::Suc(bx!(prev)), DynamicValue::Nat)
			}
		}
		CaseNat { scrutinee, motive_parameter, motive, case_nil, case_suc_parameters, case_suc } => {
			let scrutinee = verify_dynamic(context, *scrutinee, DynamicValue::Nat);
			let scrutinee_value = scrutinee.clone().evaluate(&context.environment);
			let (motive, _, _) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(motive_parameter, DynamicValue::Nat),
				*motive,
			);
			let motive_value = Closure::new(context.environment.clone(), [motive_parameter], motive.clone());
			let case_nil =
				verify_dynamic(context, *case_nil, motive_value.evaluate_with([DynamicValue::Num(0)]));
			// NOTE: I'm not entirely sure this is 'right', as motive is is formed in a smaller context, but I believe this should be 'safe' because of de Bruijn levels.
			let case_suc = verify_dynamic(
				&context.clone().bind_dynamic(case_suc_parameters.0, DynamicValue::Nat).bind_dynamic(
					case_suc_parameters.1,
					motive_value.evaluate_with([(case_suc_parameters.0, context.len()).into()]),
				),
				*case_suc,
				motive_value.evaluate_with([DynamicValue::Neutral(DynamicNeutral::Suc(rc!(
					DynamicNeutral::Variable(case_suc_parameters.0, context.len())
				)))]),
			);
			(
				DynamicTerm::CaseNat {
					scrutinee: bx!(scrutinee),
					motive: bind([motive_parameter], bx!(motive)),
					case_nil: bx!(case_nil),
					case_suc: bind([case_suc_parameters.0, case_suc_parameters.1], bx!(case_suc)),
				},
				motive_value.evaluate_with([scrutinee_value]),
			)
		}
		Bool => (
			DynamicTerm::Bool,
			DynamicValue::Universe {
				copyability: rc!(StaticValue::Copyability(Copyability::Trivial)),
				representation: rc!(StaticValue::ReprAtom(ReprAtom::Byte)),
			},
		),
		BoolValue(b) => (DynamicTerm::BoolValue(b), DynamicValue::Bool),
		CaseBool { scrutinee, motive, case_false, case_true } => {
			let scrutinee = verify_dynamic(context, *scrutinee, DynamicValue::Bool);
			let scrutinee_value = scrutinee.clone().evaluate(&context.environment);
			let (motive_term, _, _) = elaborate_dynamic_type(
				&context.clone().bind_dynamic(motive.parameter(), DynamicValue::Bool),
				*motive.body,
			);
			let motive_value = Closure::new(context.environment.clone(), motive.parameters, motive_term.clone());
			let case_false = verify_dynamic(
				context,
				*case_false,
				motive_value.evaluate_with([DynamicValue::BoolValue(false)]),
			);
			let case_true =
				verify_dynamic(context, *case_true, motive_value.evaluate_with([DynamicValue::BoolValue(true)]));
			(
				DynamicTerm::CaseBool {
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

pub fn verify_dynamic(context: &Context, term: DynamicPreterm, ty: DynamicValue) -> DynamicTerm {
	use DynamicPreterm::*;
	match (term, ty) {
		(Lambda { parameter, body }, DynamicValue::IndexedProduct { base, family, .. }) => {
			let body = verify_dynamic(
				&context.clone().bind_dynamic(parameter, base.as_ref().clone()),
				*body,
				family.evaluate_with([(parameter, context.len()).into()]),
			);
			DynamicTerm::Lambda {
				base: base.reify(context.len()).into(),
				family: family.reify(context.len()),
				body: bind([parameter], body.into()),
			}
		}
		(Pair { basepoint, fiberpoint }, DynamicValue::IndexedSum { base, family, .. }) => {
			let basepoint = verify_dynamic(context, *basepoint, base.as_ref().clone());
			let basepoint_value = basepoint.clone().evaluate(&context.environment);
			let fiberpoint = verify_dynamic(context, *fiberpoint, family.evaluate_with([basepoint_value]));
			DynamicTerm::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) }
		}
		(Let { assignee, ty, argument, tail }, _) => {
			let (ty, _, _) = elaborate_dynamic_type(context, *ty);
			let ty_value = ty.clone().evaluate(&context.environment);
			let argument = verify_dynamic(context, *argument, ty_value.clone());
			let argument_value = argument.clone().evaluate(&context.environment);
			let tail = verify_dynamic(
				&context.clone().extend(
					assignee,
					Value::Dynamic(ty_value.clone()),
					Value::Dynamic(argument_value),
				),
				*tail,
				ty_value,
			);
			DynamicTerm::Let { ty: bx!(ty), argument: bx!(argument), tail: bind([assignee], bx!(tail)) }
		}
		(WrapNew(tm), DynamicValue::WrapType(ty)) => {
			let tm = verify_dynamic(context, *tm, ty.as_ref().clone());
			DynamicTerm::WrapNew(bx!(tm))
		}
		(RcNew(tm), DynamicValue::RcType(ty)) => {
			let tm = verify_dynamic(context, *tm, ty.as_ref().clone());
			DynamicTerm::RcNew(bx!(tm))
		}
		(term, ty) => {
			let (term, synthesized_ty) = synthesize_dynamic(context, term);
			if context.len().can_convert(&synthesized_ty, &ty) {
				term
			} else {
				println!("{:#?}", term);
				panic!(
					"synthesized type {:#?} did not match expected type {:#?}",
					synthesized_ty.reify(context.len()),
					ty.reify(context.len()),
				);
			}
		}
	}
}

pub fn elaborate_dynamic_type(
	context: &Context,
	term: DynamicPreterm,
) -> (DynamicTerm, /* copyability */ StaticValue, /* representation */ StaticValue) {
	let (term, DynamicValue::Universe { copyability, representation }) = synthesize_dynamic(context, term)
	else {
		panic!("tried to elaborate a non-type dynamic term as a type");
	};
	(term, copyability.as_ref().clone(), representation.as_ref().clone())
}
