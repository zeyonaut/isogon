use std::{collections::HashMap, rc::Rc};

use crate::gamma::{
	common::{Binder, Copyability, Level, Name},
	ir::{
		closed::{Function, Procedure, Program, Substitute, Term, Variable},
		object as ob,
	},
};

/// Performs closure-conversion on an object term, hoisting all functions to top level.
pub fn close(value: ob::Term) -> Program {
	let mut closer = Closer { context: vec![], procedures: vec![] };

	let entry = closer.close(value, &mut vec![]);

	Program { entry, procedures: closer.procedures }
}

#[derive(Debug)]
struct DynamicContextEntry {
	name: Option<Name>,
	ty: ob::Term,
	dependees: Vec<bool>,
}

struct Closer {
	context: Vec<DynamicContextEntry>,
	procedures: Vec<Procedure>,
}

impl Closer {
	fn close(&mut self, value: ob::Term, is_occurrent: &mut Vec<bool>) -> Term {
		match value {
			// Variables.
			ob::Term::Variable(_, l) => {
				is_occurrent.get_mut(l.0).map(|has_encountered_l| *has_encountered_l = true);
				Term::Variable(Variable::Local(l))
			}

			// Procedures.
			ob::Term::Function { base, family: _, body } =>
				Term::Function(self.close_function((*base).clone(), body, is_occurrent)),

			// Binding cases.
			ob::Term::Let { ty, argument, tail } => Term::Let {
				ty: self.close((*ty).clone(), is_occurrent).into(),
				argument: self.close((*argument).clone(), is_occurrent).into(),
				tail: self.close_with(tail, [(*ty).clone()], is_occurrent),
			},
			ob::Term::Pi { base_universe: _, base, family_universe, family } => Term::Pi {
				base: self.close((*base).clone(), is_occurrent).into(),
				family: self.close_function((*base).clone(), family, is_occurrent),
				family_universe,
			},
			ob::Term::Sigma { base_universe, base, family_universe, family } => Term::Sigma {
				base_universe,
				base: self.close((*base).clone(), is_occurrent).into(),
				family_universe,
				family: self.close_function((*base).clone(), family, is_occurrent),
			},

			// 0-recursive cases.
			ob::Term::Nat => Term::Nat,
			ob::Term::Enum(k) => Term::Enum(k),
			ob::Term::Universe(k) => Term::Universe(k),
			ob::Term::Num(n) => Term::Num(n),
			ob::Term::EnumValue(k, v) => Term::EnumValue(k, v),

			// 1-recursive cases.
			ob::Term::Project(t, p, u) => Term::Project(self.close((*t).clone(), is_occurrent).into(), p, u),
			ob::Term::Suc(t) => Term::Suc(self.close((*t).clone(), is_occurrent).into()),
			ob::Term::WrapType(t, _) => Term::WrapType(self.close((*t).clone(), is_occurrent).into()),
			ob::Term::WrapNew(t) => Term::WrapNew(self.close((*t).clone(), is_occurrent).into()),
			ob::Term::Unwrap(t, u) => Term::Unwrap(self.close((*t).clone(), is_occurrent).into(), u),
			ob::Term::RcType(t, _) => Term::RcType(self.close((*t).clone(), is_occurrent).into()),
			ob::Term::RcNew(t) => Term::RcNew(self.close((*t).clone(), is_occurrent).into()),
			ob::Term::UnRc(t, u) => Term::UnRc(self.close((*t).clone(), is_occurrent).into(), u),

			// 2-recursive cases
			ob::Term::Pair { basepoint, fiberpoint } => Term::Pair {
				basepoint: self.close((*basepoint).clone(), is_occurrent).into(),
				fiberpoint: self.close((*fiberpoint).clone(), is_occurrent).into(),
			},
			ob::Term::Refl(t, x) => todo!(),

			ob::Term::Id { kind, space, left, right } => todo!(),

			// Other cases
			ob::Term::Apply { scrutinee, argument, fiber_universe, base, family } => Term::Apply {
				callee: self.close((*scrutinee).clone(), is_occurrent).into(),
				argument: self.close((*argument).clone(), is_occurrent).into(),
				fiber_representation: fiber_universe.1,
				// TODO: This might be problematic if a function is called more than once with a lambda-expression in its family?
				family: (fiber_universe.0 == Copyability::Nontrivial)
					.then(|| self.close_with(family, [(*base).clone()], is_occurrent)),
			},
			ob::Term::CaseNat { scrutinee, case_nil, case_suc, fiber_universe, motive } => {
				Term::CaseNat {
					scrutinee: self.close((*scrutinee).clone(), is_occurrent).into(),
					case_nil: self.close((*case_nil).clone(), is_occurrent).into(),
					// NOTE: This is an abuse of the binder system, but it seems like it should work.
					case_suc: self.close_with(case_suc, [ob::Term::Nat, (*motive.body).clone()], is_occurrent),
					fiber_representation: fiber_universe.1,
					motive: (fiber_universe.0 == Copyability::Nontrivial)
						.then(|| self.close_with(motive, [ob::Term::Nat], is_occurrent)),
				}
			}
			ob::Term::CaseEnum { scrutinee, cases, fiber_universe, motive } => {
				let cardinality: u16 = cases.len().try_into().unwrap();
				Term::CaseEnum {
					scrutinee: self.close((*scrutinee).clone(), is_occurrent).into(),
					cases: cases.into_iter().map(|case| self.close(case, is_occurrent)).collect(),
					fiber_representation: fiber_universe.1,
					motive: (fiber_universe.0 == Copyability::Nontrivial)
						.then(|| self.close_with(motive, [ob::Term::Enum(cardinality)], is_occurrent)),
				}
			}
			ob::Term::CasePath { scrutinee, motive, case_refl } => todo!(),
		}
	}

	fn close_function(
		&mut self,
		base: ob::Term,
		body: Binder<Rc<ob::Term>>,
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
		binder: Binder<Rc<ob::Term>, N>,
		tys: [ob::Term; N],
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
