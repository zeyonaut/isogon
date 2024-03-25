use std::{collections::HashMap, rc::Rc};

use super::stage::stage_as_dynamic_universe;
use crate::gamma::{
	common::{Binder, Closure, Copyability, Index, Level, Name},
	ir::{
		closed::{Function, Procedure, Program, Substitute, Term, Variable},
		object::Environment,
		syntax::{DynamicTerm, StaticTerm},
	},
};

/// Performs closure-conversion on an object term, hoisting all functions to top level.
pub fn close(value: DynamicTerm) -> Program {
	let mut closer = Closer { context: vec![], procedures: vec![] };

	let entry = closer.close(value, &mut vec![]);

	Program { entry, procedures: closer.procedures }
}

#[derive(Debug)]
struct DynamicContextEntry {
	name: Option<Name>,
	ty: DynamicTerm,
	dependees: Vec<bool>,
}

struct Closer {
	context: Vec<DynamicContextEntry>,
	procedures: Vec<Procedure>,
}

// TODO: This is silly.
const EMPTY_ENV: Environment = Environment::new();

impl Closer {
	fn close(&mut self, value: DynamicTerm, is_occurrent: &mut Vec<bool>) -> Term {
		match value {
			// Variables.
			DynamicTerm::Variable(_, Index(i)) => {
				let l = self.context.len() - (i + 1);
				is_occurrent.get_mut(l).map(|has_encountered_l| *has_encountered_l = true);
				Term::Variable(Variable::Local(Level(l)))
			}

			// Procedures.
			DynamicTerm::Function { base, family: _, body } =>
				Term::Function(self.close_function((*base).clone(), body, is_occurrent)), // FIXME: Why isn't this erroring??? Wrong function arguments!

			// Binding cases.
			DynamicTerm::Let { ty, argument, tail } => Term::Let {
				ty: self.close((*ty).clone(), is_occurrent).into(),
				argument: self.close((*argument).clone(), is_occurrent).into(),
				tail: self.close_with(tail, [(*ty).clone()], is_occurrent),
			},
			DynamicTerm::Pi { base, family, family_copyability, family_representation, .. } => Term::Pi {
				base: self.close((*base).clone(), is_occurrent).into(),
				family: self.close_function((*base).clone(), family, is_occurrent), // FIXME: Why isn't this erroring??? Wrong function arguments!
				// TODO: This is really kind of annoying; we don't really want to have to stage this again.
				// How bad would it be to define a fourth IR for the object syntax that embeds into the core syntax?
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					&EMPTY_ENV,
				),
			},
			DynamicTerm::Sigma {
				base_copyability,
				base_representation,
				base,
				family_copyability,
				family_representation,
				family,
			} => Term::Sigma {
				base_universe: stage_as_dynamic_universe(*base_copyability, *base_representation, &EMPTY_ENV),
				base: self.close((*base).clone(), is_occurrent).into(),
				family_universe: stage_as_dynamic_universe(
					*family_copyability,
					*family_representation,
					&EMPTY_ENV,
				),
				family: self.close_function((*base).clone(), family, is_occurrent), // FIXME: Why isn't this erroring??? Wrong function arguments!
			},

			// 0-recursive cases.
			DynamicTerm::Nat => Term::Nat,
			DynamicTerm::Enum(k) => Term::Enum(k),
			DynamicTerm::Universe { copyability, representation } =>
				Term::Universe(stage_as_dynamic_universe(*copyability, *representation, &EMPTY_ENV)),
			DynamicTerm::Num(n) => Term::Num(n),
			DynamicTerm::EnumValue(k, v) => Term::EnumValue(k, v),

			// 1-recursive cases.
			DynamicTerm::Project {
				scrutinee: t,
				projection: p,
				projection_copyability,
				projection_representation,
			} => {
				let u =
					stage_as_dynamic_universe(*projection_copyability, *projection_representation, &EMPTY_ENV);
				Term::Project(self.close((*t).clone(), is_occurrent).into(), p, u)
			}
			DynamicTerm::Suc(t) => Term::Suc(self.close((*t).clone(), is_occurrent).into()),
			DynamicTerm::WrapType { inner: t, .. } =>
				Term::WrapType(self.close((*t).clone(), is_occurrent).into()), // FIXME: Why isn't this erroring??? Wrong function arguments!
			DynamicTerm::WrapNew(t) => Term::WrapNew(self.close((*t).clone(), is_occurrent).into()),
			DynamicTerm::Unwrap { scrutinee: t, copyability, representation } => {
				let u = stage_as_dynamic_universe(*copyability, *representation, &EMPTY_ENV);
				Term::Unwrap(self.close((*t).clone(), is_occurrent).into(), u)
			}
			DynamicTerm::RcType { inner: t, .. } => Term::RcType(self.close((*t).clone(), is_occurrent).into()),
			DynamicTerm::RcNew(t) => Term::RcNew(self.close((*t).clone(), is_occurrent).into()),
			DynamicTerm::UnRc { scrutinee: t, copyability, representation } => {
				let u = stage_as_dynamic_universe(*copyability, *representation, &EMPTY_ENV);
				Term::UnRc(self.close((*t).clone(), is_occurrent).into(), u)
			}

			// 2-recursive cases
			DynamicTerm::Pair { basepoint, fiberpoint } => Term::Pair {
				basepoint: self.close((*basepoint).clone(), is_occurrent).into(),
				fiberpoint: self.close((*fiberpoint).clone(), is_occurrent).into(),
			},

			// Unimplemented :(
			DynamicTerm::Refl => unimplemented!(),
			DynamicTerm::Id { space, left, right, .. } => unimplemented!(),

			// Other cases
			DynamicTerm::Apply {
				scrutinee,
				argument,
				base,
				family,
				fiber_copyability,
				fiber_representation,
			} => {
				let u = stage_as_dynamic_universe(*fiber_copyability, *fiber_representation, &EMPTY_ENV);
				Term::Apply {
					callee: self.close((*scrutinee).clone(), is_occurrent).into(),
					argument: self.close((*argument).clone(), is_occurrent).into(),
					fiber_representation: u.1,
					// TODO: This might be problematic if a function is called more than once with a lambda-expression in its family?
					family: (u.0 == Copyability::Nontrivial)
						.then(|| self.close_with(family, [(*base).clone()], is_occurrent)),
				}
			}
			DynamicTerm::CaseNat {
				scrutinee,
				case_nil,
				case_suc,
				fiber_copyability,
				fiber_representation,
				motive,
			} => {
				let fiber_universe =
					stage_as_dynamic_universe(*fiber_copyability, *fiber_representation, &EMPTY_ENV);
				Term::CaseNat {
					scrutinee: self.close((*scrutinee).clone(), is_occurrent).into(),
					case_nil: self.close((*case_nil).clone(), is_occurrent).into(),
					// NOTE: This is an abuse of the binder system, but it seems like it should work.
					case_suc: self.close_with(case_suc, [DynamicTerm::Nat, (*motive.body).clone()], is_occurrent),
					fiber_representation: fiber_universe.1,
					motive: (fiber_universe.0 == Copyability::Nontrivial)
						.then(|| self.close_with(motive, [DynamicTerm::Nat], is_occurrent)),
				}
			}
			DynamicTerm::CaseEnum { scrutinee, cases, fiber_copyability, fiber_representation, motive } => {
				let cardinality: u16 = cases.len().try_into().unwrap();
				let fiber_universe =
					stage_as_dynamic_universe(*fiber_copyability, *fiber_representation, &EMPTY_ENV);
				Term::CaseEnum {
					scrutinee: self.close((*scrutinee).clone(), is_occurrent).into(),
					cases: cases.into_iter().map(|case| self.close(case, is_occurrent)).collect(),
					fiber_representation: fiber_universe.1,
					motive: (fiber_universe.0 == Copyability::Nontrivial)
						.then(|| self.close_with(motive, [DynamicTerm::Enum(cardinality)], is_occurrent)),
				}
			}
			// Unimplemented :(
			DynamicTerm::CasePath { scrutinee, motive, case_refl } => unimplemented!(),
			// TODO: Maybe this shouldn't be necessary if we use a different data type.
			DynamicTerm::Splice(_) => panic!("unexpected splice encountered."),
		}
	}

	fn close_function(
		&mut self,
		base: DynamicTerm,
		body: Binder<Box<DynamicTerm>>,
		is_occurrent: &mut Vec<bool>,
	) -> Function {
		let context_len = Level(self.context.len());

		// Find free occurrents in base and body.
		let mut body_occurrents = vec![false; context_len.0];

		let mut body = self.close_with(body, [base.clone()], &mut body_occurrents);
		let mut base = self.close(base, &mut body_occurrents);

		// Update the external free occurrence set.
		for (outer, inner) in is_occurrent.iter_mut().zip(&mut body_occurrents) {
			*outer |= *inner;
		}

		// Find dependeees in base and body.
		let dependees = self.occurrents_to_dependees(body_occurrents);

		// Construct a partial substitution from the dependees.
		let (captures, sub) = {
			let mut captures = Vec::new();
			let mut sub = HashMap::new();
			let mut count = 0;
			for (i, is_dependee) in dependees.into_iter().enumerate() {
				if is_dependee {
					captures.push(Level(i));
					sub.insert(Level(i), Level(count));
					count += 1;
				}
			}
			(captures, sub)
		};

		base.substitute(&sub, Level(self.context.len()));
		body.substitute(&sub, context_len);
		let Binder { parameters: [parameter], body } = body;

		let captured_parameters = {
			let mut captured_parameters = Vec::new();

			for i in &captures {
				let mut closed_ty = self.close(self.context[i.0].ty.clone(), is_occurrent);

				closed_ty.substitute(&sub, *i);

				captured_parameters.push((self.context[i.0].name, closed_ty))
			}
			captured_parameters
		};

		let parameter = (parameter, base);

		let procedure = Procedure { captured_parameters, parameter, body: *body };

		let procedure_id = self.procedures.len();
		self.procedures.push(procedure);

		Function { procedure_id, captures: captures.into_iter().map(Variable::Local).collect() }
	}

	fn close_with<const N: usize>(
		&mut self,
		binder: Binder<Box<DynamicTerm>, N>,
		tys: [DynamicTerm; N],
		is_occurrent: &mut Vec<bool>,
	) -> Binder<Box<Term>, N> {
		let level = self.context.len();
		for (name, ty) in binder.parameters.into_iter().zip(tys) {
			// Compute ty's dependees (occurrents and occurrents of dependees).
			let occurrents = ty.occurences(Level(self.context.len()));
			self.context.push(DynamicContextEntry {
				name,
				ty,
				dependees: self.occurrents_to_dependees(occurrents),
			});
		}
		let result = binder.mapv(|_, body| self.close((*body).clone(), is_occurrent));
		self.context.truncate(level);
		result
	}

	fn occurrents_to_dependees(&self, mut occurrents: Vec<bool>) -> Vec<bool> {
		for occurrent_index in
			occurrents.clone().into_iter().enumerate().filter_map(|(i, is_occurrent)| is_occurrent.then_some(i))
		{
			for (outer, inner) in occurrents.iter_mut().zip(self.context[occurrent_index].dependees.iter()) {
				*outer |= *inner;
			}
		}
		occurrents
	}
}

impl DynamicTerm {
	// FIXME: I don't think this properly collects occurrences in inferred types (e.g. in Rc or in a scrutinee)?
	// Yields the characteristic of the subset of all levels < level that occur as a variable in a value.
	pub fn occurences(&self, Level(level): Level) -> Vec<bool> {
		// FIXME: Move to terms with levels.
		fn mark_occurrents_bind<const N: usize>(
			binder: &Binder<Box<DynamicTerm>, N>,
			is_occurrent: &mut Vec<bool>,
			level: usize,
		) {
			mark_occurrents(&binder.body, is_occurrent, level + N);
		}

		fn mark_occurrents(value: &DynamicTerm, is_occurrent: &mut Vec<bool>, level: usize) {
			match value {
				DynamicTerm::Variable(_, Index(i)) =>
					if let Some(l_is_occurrent) = is_occurrent.get_mut(level - (i + 1)) {
						*l_is_occurrent = true;
					},

				// Cases with binders.
				DynamicTerm::Function { base, family, body } => {
					mark_occurrents(base, is_occurrent, level);
					mark_occurrents_bind(family, is_occurrent, level);
					mark_occurrents_bind(body, is_occurrent, level);
				}
				DynamicTerm::Let { ty, argument, tail } => {
					mark_occurrents(ty, is_occurrent, level);
					mark_occurrents(argument, is_occurrent, level);
					mark_occurrents_bind(tail, is_occurrent, level);
				}
				DynamicTerm::Pi { base, family, .. } | DynamicTerm::Sigma { base, family, .. } => {
					mark_occurrents(base, is_occurrent, level);
					mark_occurrents_bind(family, is_occurrent, level);
				}
				DynamicTerm::CaseNat { scrutinee, case_nil, case_suc, motive, .. } => {
					mark_occurrents(scrutinee, is_occurrent, level);
					mark_occurrents(case_nil, is_occurrent, level);
					mark_occurrents_bind(case_suc, is_occurrent, level);
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents_bind(motive, is_occurrent, level);
				}
				DynamicTerm::CaseEnum { scrutinee, cases, motive, .. } => {
					mark_occurrents(scrutinee, is_occurrent, level);
					for case in cases {
						mark_occurrents(case, is_occurrent, level);
					}
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents(&motive.body, is_occurrent, level);
				}
				DynamicTerm::CasePath { scrutinee, motive, case_refl } => {
					mark_occurrents(scrutinee, is_occurrent, level);
					mark_occurrents(case_refl, is_occurrent, level);
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents_bind(motive, is_occurrent, level);
				}

				// 0-recursive cases.
				DynamicTerm::Universe { .. }
				| DynamicTerm::Enum(_)
				| DynamicTerm::EnumValue(_, _)
				| DynamicTerm::Nat
				| DynamicTerm::Num(_)
				| DynamicTerm::Refl => (),

				// 1-recursive cases.
				DynamicTerm::Project { scrutinee: a, .. }
				| DynamicTerm::Suc(a)
				| DynamicTerm::WrapType { inner: a, .. }
				| DynamicTerm::WrapNew(a)
				| DynamicTerm::Unwrap { scrutinee: a, .. }
				| DynamicTerm::RcType { inner: a, .. }
				| DynamicTerm::RcNew(a)
				| DynamicTerm::UnRc { scrutinee: a, .. } => mark_occurrents(a, is_occurrent, level),

				// n-recursive cases.
				DynamicTerm::Pair { basepoint: a, fiberpoint: b } => {
					mark_occurrents(a, is_occurrent, level);
					mark_occurrents(b, is_occurrent, level);
				}

				DynamicTerm::Id { space: a, left: b, right: c, .. } => {
					// TODO: How much of this is actually necessary? None? Aren't these just never used?
					mark_occurrents(a, is_occurrent, level);
					mark_occurrents(b, is_occurrent, level);
					mark_occurrents(c, is_occurrent, level);
				}

				DynamicTerm::Apply { scrutinee: a, argument: b, base, family, .. } => {
					mark_occurrents(a, is_occurrent, level);
					mark_occurrents(b, is_occurrent, level);
					// TODO: Shouldn't occurrents not be marked if the fiber universe is trivial?
					mark_occurrents(base, is_occurrent, level);
					mark_occurrents_bind(family, is_occurrent, level);
				}

				// TODO: Maybe this should not be necessary?
				DynamicTerm::Splice(_) => panic!("unexpected splice"),
			}
		}

		let mut is_occurrent = vec![false; level];
		mark_occurrents(self, &mut is_occurrent, level);
		is_occurrent
	}
}
