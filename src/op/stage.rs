use crate::{
	common::{Binder, Closure, Cpy, Field, Label, Level, Repr, UniverseKind},
	ir::{
		object::{DynamicValue, Environment, StaticValue, Value},
		syntax::{DynamicTerm, KindTerm, StaticTerm},
	},
};

pub trait Stage {
	type ObjectTerm;
	/// Transforms a core term into an object term.
	fn stage(self) -> Self::ObjectTerm
	where
		Self: Sized,
	{
		self.stage_in(&Environment::new())
	}

	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm;
}

impl Stage for StaticTerm {
	type ObjectTerm = StaticValue;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		match self {
			// Variables.
			StaticTerm::Variable(_, index) => environment.lookup_static(index),

			// Let-expressions.
			StaticTerm::Let { argument, tail, .. } =>
				tail.stage_at(environment, [argument.stage_in(environment)]),

			// Types and universe indices.
			StaticTerm::Universe(_) => StaticValue::Type,

			StaticTerm::Cpy => StaticValue::Type,
			StaticTerm::CpyNt => StaticValue::CpyValue(Cpy::Nt),
			StaticTerm::CpyMax(set) => StaticValue::CpyValue(set.into_iter().fold(Cpy::Tr, |a, b| {
				let StaticValue::CpyValue(b) = b.stage_in(environment) else { panic!() };
				std::cmp::max(a, b)
			})),

			StaticTerm::Repr => StaticValue::Type,
			StaticTerm::ReprAtom(r) => StaticValue::ReprValue(r.map(Repr::Atom)),
			StaticTerm::ReprExp(n, r) => {
				let StaticValue::ReprValue(r) = r.stage_in(environment) else { panic!() };
				StaticValue::ReprValue(r.map(|r| (Repr::Exp(n, r.into()))))
			}
			StaticTerm::ReprPair(r0, r1) => {
				let StaticValue::ReprValue(r0) = r0.stage_in(environment) else { panic!() };
				let StaticValue::ReprValue(r1) = r1.stage_in(environment) else { panic!() };
				match (r0, r1) {
					(None, r1) => StaticValue::ReprValue(r1),
					(r0, None) => StaticValue::ReprValue(r0),
					(Some(r0), Some(r1)) => StaticValue::ReprValue(Some(Repr::Pair(r0.into(), r1.into()))),
				}
			}

			// Quoted programs.
			StaticTerm::Lift { .. } => StaticValue::Type,
			StaticTerm::Quote(term) => StaticValue::Quote(term.stage_in(environment).into()),

			// Repeated programs.
			StaticTerm::Exp(..) => StaticValue::Type,
			StaticTerm::Repeat(_, t) => StaticValue::Repeat(t.stage_in(environment).into()),
			StaticTerm::ExpLet { grade: _, grade_argument: _, argument, tail } => {
				let StaticValue::Repeat(v) = argument.stage_in(environment) else { panic!() };
				tail.stage_at(environment, [(*v).clone()])
			}
			StaticTerm::ExpProject(t) => {
				let StaticValue::Repeat(v) = t.stage_in(environment) else { panic!() };
				v.as_ref().clone()
			}

			// Dependent functions.
			StaticTerm::Pi { .. } => StaticValue::Type,
			StaticTerm::Function(_, function) => StaticValue::Function(function.stage_in(environment)),
			StaticTerm::Apply { scrutinee, argument } => {
				let StaticValue::Function(function) = scrutinee.stage_in(environment) else { panic!() };
				function.stage_with([argument.stage_in(environment)])
			}

			// Dependent pairs.
			StaticTerm::Sg { .. } => StaticValue::Type,
			StaticTerm::Pair { basepoint, fiberpoint } =>
				StaticValue::Pair(basepoint.stage_in(environment).into(), fiberpoint.stage_in(environment).into()),
			StaticTerm::SgField(scrutinee, projection) => {
				let StaticValue::Pair(basepoint, fiberpoint) = scrutinee.stage_in(environment) else { panic!() };
				match projection {
					Field::Base => basepoint.as_ref().clone(),
					Field::Fiber => fiberpoint.as_ref().clone(),
				}
			}
			StaticTerm::SgLet { grade: _, argument, tail } => {
				let StaticValue::Pair(basepoint, fiberpoint) = argument.stage_in(environment) else { panic!() };
				tail.stage_at(environment, [(*basepoint).clone(), (*fiberpoint).clone()])
			}

			// Enumerated numbers.
			StaticTerm::Enum(_) => StaticValue::Type,
			StaticTerm::EnumValue(_, v) => StaticValue::EnumValue(v),
			StaticTerm::CaseEnum { scrutinee, motive: _, cases } => {
				let StaticValue::EnumValue(v) = scrutinee.stage_in(environment) else { panic!() };
				cases.into_iter().nth(v as _).unwrap().stage_in(environment)
			}

			// Natural numbers.
			StaticTerm::Nat => StaticValue::Type,
			StaticTerm::Num(n) => StaticValue::NatValue(n),
			StaticTerm::Suc(p) => {
				let StaticValue::NatValue(p) = p.stage_in(environment) else { panic!() };
				StaticValue::NatValue(p + 1)
			}
			StaticTerm::CaseNat { scrutinee, motive: _, case_nil, case_suc } => {
				let StaticValue::NatValue(n) = scrutinee.stage_in(environment) else { panic!() };
				(0..n).fold(case_nil.stage_in(environment), |previous, i| {
					case_suc.clone().stage_at(environment, [StaticValue::NatValue(i), previous])
				})
			}
		}
	}
}

impl Stage for DynamicTerm {
	type ObjectTerm = DynamicValue;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		use DynamicTerm::*;
		match self {
			// Variables.
			Variable(_, index) => environment.lookup_dynamic(index),

			// Let-expressions.
			Def { grade: _, ty: _, argument, tail } =>
				tail.body.stage_in(&environment.extend([Value::Static(argument.stage_in(environment))])),
			Let { grade, ty, argument_kind, argument, tail } => DynamicValue::Let {
				grade,
				ty_kind: argument_kind.stage_in(environment),
				ty: ty.stage_in(environment).into(),
				argument: argument.stage_in(environment).into(),
				tail: tail.stage_in(environment),
			},

			// Types.
			Universe { kind } => DynamicValue::Universe(kind.stage_in(environment)),

			// Quoted programs.
			Splice(term) => {
				let StaticValue::Quote(value) = term.stage_in(environment) else { panic!() };
				value.as_ref().clone()
			}

			// Repeated programs.
			Exp(n, kind, ty) =>
				DynamicValue::Exp(n, kind.stage_in(environment), ty.stage_in(environment).into()),
			Repeat(n, tm) => DynamicValue::Repeat(n, tm.stage_in(environment).into()),
			ExpLet { grade, grade_argument, argument, kind, tail } => DynamicValue::ExpLet {
				grade,
				grade_argument,
				argument: argument.stage_in(environment).into(),
				kind: kind.stage_in(environment),
				tail: tail.stage_in(environment),
			},
			ExpProject(t) => DynamicValue::ExpProject(t.stage_in(environment).into()),

			// Dependent functions.
			Pi { grade, base_kind, base, family_kind, family } => DynamicValue::Pi {
				grade,
				base_kind: base_kind.stage_in(environment),
				base: base.stage_in(environment).into(),
				family_kind: family_kind.stage_in(environment),
				family: family.stage_in(environment),
			},
			Function { grade, body, domain_kind, codomain_kind } => DynamicValue::Function {
				grade,
				body: body.stage_in(environment),
				domain_kind: domain_kind.map(|kind| kind.stage_in(environment)),
				codomain_kind: codomain_kind.map(|kind| kind.stage_in(environment)),
			},
			Apply { scrutinee, grade, argument, family_kind } => DynamicValue::Apply {
				scrutinee: scrutinee.stage_in(environment).into(),
				grade,
				argument: argument.stage_in(environment).into(),
				family_kind: family_kind.map(|kind| kind.stage_in(environment)),
			},

			// Dependent pairs.
			Sg { base_kind, base, family_kind, family } => DynamicValue::Sg {
				base_kind: base_kind.stage_in(environment),
				base: base.stage_in(environment).into(),
				family_kind: family_kind.stage_in(environment),
				family: family.stage_in(environment),
			},
			Pair { basepoint, fiberpoint } => DynamicValue::Pair {
				basepoint: basepoint.stage_in(environment).into(),
				fiberpoint: fiberpoint.stage_in(environment).into(),
			},
			SgField { scrutinee, field } => DynamicValue::SgField(scrutinee.stage_in(environment).into(), field),
			SgLet { grade, argument, kinds, tail } => DynamicValue::SgLet {
				grade,
				argument: argument.stage_in(environment).into(),
				kinds: kinds.map(|kind| kind.stage_in(environment)),
				tail: tail.stage_in(environment),
			},

			// Enumerated numbers.
			Enum(k) => DynamicValue::Enum(k),
			EnumValue(k, v) => DynamicValue::EnumValue(k, v),
			CaseEnum { scrutinee, motive_kind, motive, cases } => DynamicValue::CaseEnum {
				scrutinee: scrutinee.stage_in(environment).into(),
				motive_kind: motive_kind.map(|kind| kind.stage_in(environment)),
				motive: motive.stage_in(environment),
				cases: cases.into_iter().map(|case| case.stage_in(environment)).collect(),
			},

			// Paths.
			Id { kind, space, left, right } => DynamicValue::Id {
				kind: kind.stage_in(environment),
				space: space.stage_in(environment).into(),
				left: left.stage_in(environment).into(),
				right: right.stage_in(environment).into(),
			},
			Refl => DynamicValue::Refl,
			CasePath { scrutinee, motive, case_refl } => DynamicValue::CasePath {
				scrutinee: scrutinee.stage_in(environment).into(),
				motive: motive.stage_in(environment),
				case_refl: case_refl.stage_in(environment).into(),
			},

			// Natural numbers.
			Nat => DynamicValue::Nat,
			Num(n) => DynamicValue::Num(n),
			Suc(prev) => DynamicValue::Suc(prev.stage_in(environment).into()),
			CaseNat { scrutinee, motive_kind, motive, case_nil, case_suc } => DynamicValue::CaseNat {
				scrutinee: scrutinee.stage_in(environment).into(),
				motive_kind: motive_kind.map(|kind| kind.stage_in(environment)),
				motive: motive.stage_in(environment),
				case_nil: case_nil.stage_in(environment).into(),
				case_suc: case_suc.stage_in(environment),
			},

			// Wrappers.
			Bx { kind, inner } =>
				DynamicValue::Bx(inner.stage_in(environment).into(), kind.stage_in(environment)),
			BxValue(x) => DynamicValue::BxValue(x.stage_in(environment).into()),
			BxProject { scrutinee, kind } => DynamicValue::BxProject(
				scrutinee.stage_in(environment).into(),
				kind.map(|kind| kind.stage_in(environment)),
			),

			Wrap { kind, inner } =>
				DynamicValue::Wrap(inner.stage_in(environment).into(), kind.stage_in(environment)),
			WrapValue(x) => DynamicValue::WrapValue(x.stage_in(environment).into()),
			WrapProject { scrutinee, kind } => DynamicValue::WrapProject(
				scrutinee.stage_in(environment).into(),
				kind.map(|kind| kind.stage_in(environment)),
			),
		}
	}
}

impl Stage for KindTerm {
	type ObjectTerm = UniverseKind;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		let StaticValue::CpyValue(copy) = self.copy.stage_in(environment) else { panic!() };
		let StaticValue::ReprValue(repr) = self.repr.stage_in(environment) else { panic!() };
		UniverseKind { copy, repr }
	}
}

impl<const N: usize> Stage for Binder<Label, Box<StaticTerm>, N> {
	type ObjectTerm = Closure<Environment, StaticTerm, N>;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

impl<const N: usize> Stage for Binder<Label, Box<DynamicTerm>, N> {
	type ObjectTerm = Closure<Environment, DynamicTerm, N>;
	fn stage_in(self, environment: &Environment) -> Self::ObjectTerm {
		Closure::new(environment.clone(), self.parameters, *self.body)
	}
}

pub trait StageWith<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_with(self, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageWith<N> for &Closure<Environment, DynamicTerm, N> {
	type ObjectTerm = DynamicValue;
	fn stage_with(self, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.clone().stage_in(&self.environment.extend(terms.map(Value::Dynamic)))
	}
}

impl<const N: usize> StageWith<N> for &Closure<Environment, StaticTerm, N> {
	type ObjectTerm = StaticValue;
	fn stage_with(self, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.clone().stage_in(&self.environment.extend(terms.map(Value::Static)))
	}
}

pub trait StageAt<const N: usize> {
	type ObjectTerm;
	/// Transforms a core term under a binder into an object term, taking arguments.
	fn stage_at(self, environment: &Environment, arguments: [Self::ObjectTerm; N]) -> Self::ObjectTerm;
}

impl<const N: usize> StageAt<N> for Binder<Label, Box<DynamicTerm>, N> {
	type ObjectTerm = DynamicValue;
	fn stage_at(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&environment.extend(terms.map(Value::Dynamic)))
	}
}

impl<const N: usize> StageAt<N> for Binder<Label, Box<StaticTerm>, N> {
	type ObjectTerm = StaticValue;
	fn stage_at(self, environment: &Environment, terms: [Self::ObjectTerm; N]) -> Self::ObjectTerm {
		self.body.stage_in(&environment.extend(terms.map(Value::Static)))
	}
}

pub trait StageAuto {
	type Value;
	/// Evaluates a closure on its own parameters by postulating them and passing them in.
	fn stage_auto(&self, context_len: Level) -> Self::Value;
}

impl<const N: usize> StageAuto for Closure<Environment, DynamicTerm, N> {
	type Value = DynamicValue;
	fn stage_auto(&self, context_len: Level) -> Self::Value {
		let mut x = 0;
		self.stage_with(self.parameters.map(|parameter| {
			let y = context_len + x;
			x += 1;
			DynamicValue::Variable(parameter, y)
		}))
	}
}
