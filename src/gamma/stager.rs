use std::{fmt::Debug, rc::Rc};

use super::{
	common::{Binder, Closure, Copyability, Index, Level, Name, Projection, Repr, ReprAtom, UniverseKind},
	elaborator::{DynamicTerm, StaticTerm},
	evaluator::{Reify, StaticValue},
};
use crate::utility::{bx, rc};

#[derive(Clone)]
pub enum Metavalue {
	Type,
	Quote(Rc<Obterm>),
	Function(Closure<Environment, StaticTerm>),
	Pair(Rc<Self>, Rc<Self>),
	Num(usize),
	BoolValue(bool),
	Copyability(Copyability),
	Repr(Option<Repr>),
}

impl Debug for Metavalue {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		match self {
			Self::Type => write!(f, "Type"),
			Self::Quote(quotee) => f.debug_tuple("Quote").field(quotee).finish(),
			Self::Function(_) => f.debug_tuple("Function").field(&format_args!("_")).finish(),
			_ => write!(f, "<...>"),
		}
	}
}

#[derive(Clone, Debug)]
pub enum Obterm {
	Variable(Name, Level),
	Let {
		ty: Rc<Self>,
		argument: Rc<Self>,
		tail: Binder<Rc<Self>>,
	},
	Universe(UniverseKind),
	Pi {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Binder<Rc<Self>>,
	},
	Function {
		// TODO: This is kind of redundant, since binders store parameter names and arity,
		// and family and body should have the same of both; the single parameter is also
		// associated with the base. Is it possible to have a more generic binder type that
		// can accommodate this extra data, but without significantly affecting existing binder code?
		base: Rc<Self>,
		family: Binder<Rc<Self>>,
		body: Binder<Rc<Self>>,
	},
	Apply {
		scrutinee: Rc<Self>,
		argument: Rc<Self>,
	},
	Sigma {
		base_universe: UniverseKind,
		base: Rc<Self>,
		family_universe: UniverseKind,
		family: Binder<Rc<Self>>,
	},
	Pair {
		basepoint: Rc<Self>,
		fiberpoint: Rc<Self>,
	},
	Project(Rc<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Rc<Self>),
	CaseNat {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_nil: Rc<Self>,
		case_suc: Binder<Rc<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Rc<Self>,
		motive: Binder<Rc<Self>>,
		case_false: Rc<Self>,
		case_true: Rc<Self>,
	},
	WrapType(Rc<Self>),
	WrapNew(Rc<Self>),
	Unwrap(Rc<Self>),
	RcType(Rc<Self>),
	RcNew(Rc<Self>),
	UnRc(Rc<Self>),
}

#[derive(Clone, Debug)]
pub enum Value {
	Static(Metavalue),
	Dynamic(Name, Level),
}

#[derive(Clone)]
pub struct Environment {
	values: Vec<Value>,
	dynamic_context_length: Level,
}

impl Environment {
	pub fn new() -> Self {
		Self { values: Vec::new(), dynamic_context_length: Level(0) }
	}

	pub fn lookup_static(&self, Index(i): Index) -> Metavalue {
		let Some(Value::Static(value)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		value.clone()
	}
	pub fn lookup_dynamic(&self, Index(i): Index) -> Obterm {
		let Some(Value::Dynamic(name, level)) = self.values.get(self.values.len() - 1 - i) else { panic!() };
		Obterm::Variable(*name, *level)
	}

	#[must_use]
	pub fn bind<const N: usize>(&self, names: [Name; N]) -> Self {
		let mut environment = self.clone();
		for name in names {
			environment.values.push(Value::Dynamic(name, environment.dynamic_context_length));
			environment.dynamic_context_length += 1;
		}
		environment
	}

	#[must_use]
	pub fn extend<const N: usize>(&self, values: [Value; N]) -> Self {
		let mut environment = self.clone();
		environment.values.extend(values);
		environment
	}
}

pub trait Stage {
	type ObjectTerm;
	/// Transforms a core term into an object term.
	fn stage(self, environment: &Environment) -> Self::ObjectTerm;
}

impl<const N: usize> Stage for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Closure<Environment, StaticTerm, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl Stage for StaticTerm {
	type ObjectTerm = Metavalue;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		use StaticTerm::*;
		match self {
			Variable(_, index) => environment.lookup_static(index),
			CopyabilityType => Metavalue::Type,
			Copyability(c) => Metavalue::Copyability(c),
			MaxCopyability(a, b) => {
				let Metavalue::Copyability(a) = a.stage(environment) else { panic!() };
				let Metavalue::Copyability(b) = b.stage(environment) else { panic!() };
				Metavalue::Copyability(std::cmp::max(a, b))
			}
			Lambda(function) => Metavalue::Function(function.stage(environment)),
			Apply { scrutinee, argument } => {
				let Metavalue::Function(function) = scrutinee.stage(environment) else { panic!() };
				// TODO: The environment argument is useless in this position: make a separate trait for this (as in EvaluateWith/EvaluateAt).
				function.stage_with(environment, [argument.stage(environment)])
			}
			Pi(..) => Metavalue::Type,
			Sigma(..) => Metavalue::Type,
			Pair { basepoint, fiberpoint } =>
				Metavalue::Pair(rc!(basepoint.stage(environment)), rc!(fiberpoint.stage(environment))),
			Project(scrutinee, projection) => {
				let Metavalue::Pair(basepoint, fiberpoint) = scrutinee.stage(environment) else { panic!() };
				match projection {
					Projection::Base => basepoint.as_ref().clone(),
					Projection::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			Let { argument, tail, .. } => tail.stage_with(environment, [argument.stage(environment)]),
			Universe => Metavalue::Type,
			Lift(_) => Metavalue::Type,
			Quote(term) => Metavalue::Quote(rc!(term.stage(environment))),
			Nat => Metavalue::Type,
			Num(n) => Metavalue::Num(n),
			Suc(p) => {
				let Metavalue::Num(p) = p.stage(environment) else { panic!() };
				Metavalue::Num(p + 1)
			}
			CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let Metavalue::Num(n) = scrutinee.stage(environment) else { panic!() };
				(0..n).fold(case_nil.stage(environment), |previous, i| {
					case_suc.clone().stage_with(environment, [Metavalue::Num(i), previous])
				})
			}
			Bool => Metavalue::Type,
			BoolValue(b) => Metavalue::BoolValue(b),
			CaseBool { scrutinee, motive: _, case_false, case_true } => {
				let Metavalue::BoolValue(b) = scrutinee.stage(environment) else { panic!() };
				if b { case_true } else { case_false }.stage(environment)
			}
			ReprType => Metavalue::Type,
			ReprAtom(r) => Metavalue::Repr(r.map(Repr::Atom)),
			ReprPair(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Pair(rc!(r0), rc!(r1)))),
				}
			}
			ReprMax(r0, r1) => {
				let Metavalue::Repr(r0) = r0.stage(environment) else { panic!() };
				let Metavalue::Repr(r1) = r1.stage(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => Metavalue::Repr(r1),
					(r0, None) => Metavalue::Repr(r0),
					(Some(r0), Some(r1)) => Metavalue::Repr(Some(Repr::Max(rc!(r0), rc!(r1)))),
				}
			}
			ReprUniv(c) => {
				let Metavalue::Copyability(c) = c.stage(environment) else { panic!() };
				match c {
					self::Copyability::Trivial => Metavalue::Repr(None),
					self::Copyability::Nontrivial => Metavalue::Repr(Some(Repr::Atom(self::ReprAtom::Class))),
				}
			}
		}
	}
}

impl<const N: usize> Stage for Binder<Box<DynamicTerm>, N> {
	type ObjectTerm = Binder<Rc<Obterm>, N>;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		self.mapv(|parameters, body| body.stage(&environment.bind(parameters)))
	}
}

fn stage_as_dynamic_universe(
	copyability: StaticValue,
	representation: StaticValue,
	environment: &Environment,
) -> UniverseKind {
	let Metavalue::Copyability(c) = copyability.reify(Level(0)).stage(environment) else { panic!() };
	let Metavalue::Repr(r) = representation.reify(Level(0)).stage(environment) else { panic!() };
	UniverseKind(c, r)
}

impl Stage for DynamicTerm {
	type ObjectTerm = Obterm;
	fn stage(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			Variable(_, index) => environment.lookup_dynamic(index),
			Lambda { base, family, body } => Obterm::Function {
				base: base.stage(environment).into(),
				body: body.stage(environment).into(),
				family: family.stage(environment).into(),
			},
			Pair { basepoint, fiberpoint } => Obterm::Pair {
				basepoint: rc!(basepoint.stage(environment)),
				fiberpoint: rc!(fiberpoint.stage(environment)),
			},
			Apply { scrutinee, argument } => Obterm::Apply {
				scrutinee: rc!(scrutinee.stage(environment)),
				argument: rc!(argument.stage(environment)),
			},
			Project(scrutinee, projection) => Obterm::Project(rc!(scrutinee.stage(environment)), projection),
			Pi {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => Obterm::Pi {
				base_universe: stage_as_dynamic_universe(base_copyability, base_representation, environment),
				base: rc!(base.stage(environment)),
				family_universe: stage_as_dynamic_universe(
					family_copyability,
					family_representation,
					environment,
				),
				family: family.stage(environment),
			},
			Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => Obterm::Sigma {
				base_universe: stage_as_dynamic_universe(base_copyability, base_representation, environment),
				base: rc!(base.stage(environment)),
				family_universe: stage_as_dynamic_universe(
					family_copyability,
					family_representation,
					environment,
				),
				family: family.stage(environment),
			},
			Let { ty, argument, tail } => Obterm::Let {
				ty: rc!(ty.stage(environment)),
				argument: rc!(argument.stage(environment)),
				tail: tail.stage(environment),
			},
			Universe { copyability, representation } => {
				let Metavalue::Copyability(c) = copyability.stage(environment) else { panic!() };
				let Metavalue::Repr(r) = representation.stage(environment) else { panic!() };
				Obterm::Universe(UniverseKind(c, r))
			}
			Splice(term) => {
				let Metavalue::Quote(value) = term.stage(environment) else { panic!() };
				value.as_ref().clone()
			}
			Nat => Obterm::Nat,
			Num(n) => Obterm::Num(n),
			Suc(prev) => Obterm::Suc(rc!(prev.stage(environment))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => Obterm::CaseNat {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_nil: rc!(case_nil.stage(environment)),
				case_suc: case_suc.stage(environment),
			},
			Bool => Obterm::Bool,
			BoolValue(b) => Obterm::BoolValue(b),
			CaseBool { scrutinee, motive, case_false, case_true } => Obterm::CaseBool {
				scrutinee: rc!(scrutinee.stage(environment)),
				motive: motive.stage(environment),
				case_false: rc!(case_false.stage(environment)),
				case_true: rc!(case_true.stage(environment)),
			},
			WrapType(x) => Obterm::WrapType(rc!(x.stage(environment))),
			WrapNew(x) => Obterm::WrapNew(rc!(x.stage(environment))),
			Unwrap(x) => Obterm::Unwrap(rc!(x.stage(environment))),
			RcType(x) => Obterm::RcType(rc!(x.stage(environment))),
			RcNew(x) => Obterm::RcNew(rc!(x.stage(environment))),
			UnRc(x) => Obterm::UnRc(rc!(x.stage(environment))),
		}
	}
}

pub trait StageWith<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_with(self, environment: &Environment, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageWith<N> for Binder<Box<StaticTerm>, N> {
	type ObjectTerm = Metavalue;
	fn stage_with(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage(&environment.extend(terms.map(Value::Static)))
	}
}

impl<const N: usize> StageWith<N> for Closure<Environment, StaticTerm, N> {
	type ObjectTerm = Metavalue;
	fn stage_with(self, _: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage(&self.environment.extend(terms.map(Value::Static)))
	}
}

pub trait Unstage {
	type CoreTerm;
	/// Transforms an object term into a core term.
	fn unstage(&self, context_len: Level) -> Self::CoreTerm;
}

impl<const N: usize> Unstage for Binder<Rc<Obterm>, N> {
	type CoreTerm = Binder<Box<DynamicTerm>, N>;
	fn unstage(&self, context_len: Level) -> Self::CoreTerm {
		self.map_ref(|body| bx!(body.unstage(context_len + N)))
	}
}

impl Unstage for Repr {
	type CoreTerm = StaticTerm;
	fn unstage(&self, level: Level) -> Self::CoreTerm {
		match self {
			Repr::Atom(r) => StaticTerm::ReprAtom(Some(*r)),
			Repr::Pair(r0, r1) => StaticTerm::ReprPair(bx!(r0.unstage(level)), bx!(r1.unstage(level))),
			Repr::Max(r0, r1) => StaticTerm::ReprMax(bx!(r0.unstage(level)), bx!(r1.unstage(level))),
		}
	}
}

impl Unstage for Obterm {
	type CoreTerm = DynamicTerm;
	fn unstage(&self, level @ Level(context_len): Level) -> Self::CoreTerm {
		use Obterm::*;
		match self {
			Variable(name, Level(variable)) => DynamicTerm::Variable(*name, Index(context_len - 1 - variable)),
			Function { base, family, body } => DynamicTerm::Lambda {
				base: base.unstage(level).into(),
				family: family.unstage(level),
				body: body.unstage(level),
			},
			Pair { basepoint, fiberpoint } => DynamicTerm::Pair {
				basepoint: bx!(basepoint.unstage(level)),
				fiberpoint: bx!(fiberpoint.unstage(level)),
			},
			Apply { scrutinee, argument } => DynamicTerm::Apply {
				scrutinee: bx!(scrutinee.unstage(level)),
				argument: bx!(argument.unstage(level)),
			},
			Project(scrutinee, projection) => DynamicTerm::Project(bx!(scrutinee.unstage(level)), *projection),
			Pi { base_universe, base, family_universe, family } => DynamicTerm::Pi {
				base_copyability: StaticValue::Copyability(base_universe.0),
				base_representation: base_universe.1.as_ref().into(),
				base: bx!(base.unstage(level)),
				family: family.unstage(level),
				family_copyability: StaticValue::Copyability(family_universe.0),
				family_representation: family_universe.1.as_ref().into(),
			},
			Sigma { base_universe, base, family_universe, family } => DynamicTerm::Sigma {
				base_copyability: StaticValue::Copyability(base_universe.0),
				base_representation: base_universe.1.as_ref().into(),
				base: bx!(base.unstage(level)),
				family: family.unstage(level),
				family_copyability: StaticValue::Copyability(family_universe.0),
				family_representation: family_universe.1.as_ref().into(),
			},
			Let { ty, argument, tail } => DynamicTerm::Let {
				ty: bx!(ty.unstage(level)),
				argument: bx!(argument.unstage(level)),
				tail: tail.unstage(level),
			},
			Universe(UniverseKind(copyability, representation)) => DynamicTerm::Universe {
				copyability: bx!(StaticTerm::Copyability(*copyability)),
				representation: bx!(representation
					.clone()
					.map(|representation| representation.unstage(level))
					.unwrap_or(StaticTerm::ReprAtom(None))),
			},
			Nat => DynamicTerm::Nat,
			Num(n) => DynamicTerm::Num(*n),
			Suc(prev) => DynamicTerm::Suc(bx!(prev.unstage(level))),
			CaseNat { scrutinee, motive, case_nil, case_suc } => DynamicTerm::CaseNat {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_nil: bx!(case_nil.unstage(level)),
				case_suc: case_suc.unstage(level),
			},
			Bool => DynamicTerm::Bool,
			BoolValue(b) => DynamicTerm::BoolValue(*b),
			CaseBool { scrutinee, motive, case_false, case_true } => DynamicTerm::CaseBool {
				scrutinee: bx!(scrutinee.unstage(level)),
				motive: motive.unstage(level),
				case_false: bx!(case_false.unstage(level)),
				case_true: bx!(case_true.unstage(level)),
			},
			WrapType(x) => DynamicTerm::WrapType(bx!(x.unstage(level))),
			WrapNew(x) => DynamicTerm::WrapNew(bx!(x.unstage(level))),
			Unwrap(x) => DynamicTerm::Unwrap(bx!(x.unstage(level))),
			RcType(x) => DynamicTerm::RcType(bx!(x.unstage(level))),
			RcNew(x) => DynamicTerm::RcNew(bx!(x.unstage(level))),
			UnRc(x) => DynamicTerm::UnRc(bx!(x.unstage(level))),
		}
	}
}
