use std::{collections::HashMap, rc::Rc};

use crate::gamma::{
	common::{Binder, Level, Name},
	ir::{
		closed::{ClosedValue, Function, Procedure, Program, Substitute, Variable},
		object::Obterm,
	},
};

#[derive(Debug)]
struct DynamicContextEntry {
	name: Name,
	ty: Obterm,
	dependees: Vec<bool>,
}

pub fn close(value: Obterm) -> Program {
	let mut closer = Closer { context: vec![], procedures: vec![] };

	let entry = closer.close(value, &mut vec![]);

	Program { entry, procedures: closer.procedures }
}

struct Closer {
	context: Vec<DynamicContextEntry>,
	procedures: Vec<Procedure>,
}

impl Closer {
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

	fn close_with<const N: usize>(
		&mut self,
		binder: Binder<Rc<Obterm>, N>,
		tys: [Obterm; N],
		is_occurrent: &mut Vec<bool>,
	) -> Binder<Box<ClosedValue>, N> {
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

	fn close_function(
		&mut self,
		base: Obterm,
		body: Binder<Rc<Obterm>>,
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

		// Find dependents in base and body.
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
				// TODO: Shouldn't these types be constrained 'values' of some sort? Otherwise, stages later down the
				// pipeline will have to deal with evaluation again to get rid of function calls,
				// projections... (Even if they aren't present at this stage, which I'm unsure of.)
				let mut closed_ty = self.close(self.context[i.0].ty.clone(), is_occurrent);

				// NOTE/(TODO: verify?): This should not panic, as its dependencies should be included.
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

	fn close(&mut self, value: Obterm, is_occurrent: &mut Vec<bool>) -> ClosedValue {
		use Obterm as Dv;
		match value {
			// Variables.
			Dv::Variable(_, l) => {
				if let Some(has_encountered) = is_occurrent.get_mut(l.0) {
					*has_encountered = true;
				}

				ClosedValue::Variable(Variable::Local(l))
			}

			// Procedures.
			Dv::Function { base, family: _, body } =>
				ClosedValue::Function(self.close_function((*base).clone(), body, is_occurrent)),

			// Binding cases.
			Dv::Let { ty, argument, tail } => {
				let closed_ty = self.close((*ty).clone(), is_occurrent);
				let argument = self.close((*argument).clone(), is_occurrent);
				let tail = self.close_with(tail, [(*ty).clone()], is_occurrent);
				ClosedValue::Let { ty: closed_ty.into(), argument: argument.into(), tail }
			}
			Dv::Pi { base_universe: _, base, family_universe: _, family } => {
				let closed_base = self.close((*base).clone(), is_occurrent);
				ClosedValue::Pi(closed_base.into(), self.close_function((*base).clone(), family, is_occurrent))
			}
			Dv::Sigma { base_universe: _, base, family_universe: _, family } => {
				let closed_base = self.close((*base).clone(), is_occurrent);
				// FIXME: This is completely wrong, we need to infer the universe of base (or otherwise store that information in the variant beforehand.)
				ClosedValue::Sigma(closed_base.into(), self.close_function((*base).clone(), family, is_occurrent))
			}
			Dv::CaseNat { scrutinee, motive, case_nil, case_suc } => {
				// TODO/FIXME: This is bad, we're manually instantiating binders with their types.
				// This is extremely error-prone; these binders should already be aware of what type they're binding.
				// (In addition, as before, the types should almost certainly be distinguished from the object syntax.)
				// Since we always know what the type of these binders should be, it suggests that these binders should
				// be a trait and not a struct, as it is right now.
				let scrutinee = self.close((*scrutinee).clone(), is_occurrent);
				// TODO: remove unnecessary clone here.
				let closed_motive = self.close_with(motive.clone(), [Obterm::Nat], is_occurrent);
				let case_nil = self.close((*case_nil).clone(), is_occurrent);
				// NOTE: This is an abuse of the binder system, but it seems like it should work.
				let case_suc = self.close_with(case_suc, [Obterm::Nat, (*motive.body).clone()], is_occurrent);
				ClosedValue::CaseNat {
					scrutinee: scrutinee.into(),
					motive: closed_motive,
					case_nil: case_nil.into(),
					case_suc: case_suc.into(),
				}
			}
			Dv::CaseBool { scrutinee, motive, case_false, case_true } => {
				let scrutinee = self.close((*scrutinee).clone(), is_occurrent);
				let motive = self.close_with(motive.clone(), [Obterm::Nat], is_occurrent);
				let case_false = self.close((*case_false).clone(), is_occurrent);
				let case_true = self.close((*case_true).clone(), is_occurrent);
				ClosedValue::CaseBool {
					scrutinee: scrutinee.into(),
					motive,
					case_false: case_false.into(),
					case_true: case_true.into(),
				}
			}

			// 0-recursive cases.
			Dv::Nat => ClosedValue::Nat,
			Dv::Bool => ClosedValue::Bool,
			Dv::Universe(k) => ClosedValue::Universe(k),
			Dv::Num(n) => ClosedValue::Num(n),
			Dv::BoolValue(b) => ClosedValue::BoolValue(b),

			// 1-recursive cases.
			Dv::Project(t, p) => ClosedValue::Project(self.close((*t).clone(), is_occurrent).into(), p),
			Dv::Suc(t) => ClosedValue::Suc(self.close((*t).clone(), is_occurrent).into()),
			Dv::WrapType(t) => ClosedValue::WrapType(self.close((*t).clone(), is_occurrent).into()),
			Dv::WrapNew(t) => ClosedValue::WrapNew(self.close((*t).clone(), is_occurrent).into()),
			Dv::Unwrap(t) => ClosedValue::Unwrap(self.close((*t).clone(), is_occurrent).into()),
			Dv::RcType(t) => ClosedValue::RcType(self.close((*t).clone(), is_occurrent).into()),
			Dv::RcNew(t) => ClosedValue::RcNew(self.close((*t).clone(), is_occurrent).into()),
			Dv::UnRc(t) => ClosedValue::UnRc(self.close((*t).clone(), is_occurrent).into()),

			// 2-recursive cases
			Dv::Apply { scrutinee, argument } => ClosedValue::Apply {
				callee: self.close((*scrutinee).clone(), is_occurrent).into(),
				argument: self.close((*argument).clone(), is_occurrent).into(),
			},
			Dv::Pair { basepoint, fiberpoint } => ClosedValue::Pair {
				basepoint: self.close((*basepoint).clone(), is_occurrent).into(),
				fiberpoint: self.close((*fiberpoint).clone(), is_occurrent).into(),
			},
		}
	}
}
