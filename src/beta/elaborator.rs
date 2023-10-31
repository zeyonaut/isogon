// TODO: solution for metas is at 1:51:00

use std::rc::Rc;

use bitvec::vec::BitVec;

use super::{
	common::{Index, Name},
	domain::{evaluate, Environment, Level, Value},
	meta::Metacontext,
	presyntax::{Preterm, RawEliminator},
	syntax::{Eliminator, Term},
};
use crate::utility::{bx, rc};

pub fn solve() {}

#[derive(Clone)]
pub struct Context {
	environment: Environment,
	tys: Vec<(Name, Rc<Value>)>, // Most recent last
	is_abstract: BitVec,
}

impl Context {
	pub fn empty() -> Self {
		Self { environment: Vec::new(), tys: Vec::new(), is_abstract: BitVec::new() }
	}

	pub fn len(&self) -> Level {
		Level(self.environment.len())
	}

	pub fn bind(mut self, name: Name, ty: Rc<Value>) -> Self {
		self.environment.push(rc!(Value::variable(self.len())));
		self.tys.push((name, ty));
		self.is_abstract.push(false);
		self
	}

	pub fn extend(mut self, name: Name, ty: Rc<Value>, value: Rc<Value>) -> Self {
		self.environment.push(value);
		self.tys.push((name, ty));
		self.is_abstract.push(true);
		self
	}
}

// Bidirectional elaboration. Verify or synthesize the type of the term in the context.
pub fn verify(
	metacontext: &mut Metacontext,
	context: &Context,
	term: Preterm,
	ty: Rc<Value>,
) -> Option<Term> {
	match (term, ty.as_ref()) {
		(Preterm::Lambda { parameter, body }, Value::Pi { parameter: _, base, family }) => {
			let body = verify(
				metacontext,
				&context.clone().bind(parameter.clone(), base.clone()),
				*body,
				family.clone().apply_value(rc!(Value::variable(context.len()))),
			)?;
			Some(Term::Lambda { parameter, body: bx!(body) })
		}
		(Preterm::Pair { basepoint, fiberpoint }, Value::Sigma { parameter: _, base, family }) => {
			let basepoint = verify(metacontext, context, *basepoint, base.clone())?;
			let basepoint_value = evaluate(context.environment.clone(), basepoint.clone());
			let fiberpoint =
				verify(metacontext, context, *fiberpoint, family.clone().apply_value(basepoint_value))?;
			Some(Term::Pair { basepoint: bx!(basepoint), fiberpoint: bx!(fiberpoint) })
		}
		(Preterm::Let { assignee, ty: argument_ty, argument, tail }, _) => {
			let argument_ty = verify(metacontext, context, *argument_ty, rc!(Value::Universe))?;
			let argument_ty_value = evaluate(context.environment.clone(), argument_ty.clone());
			let argument = verify(metacontext, context, *argument, argument_ty_value.clone())?;
			let argument_value = evaluate(context.environment.clone(), argument.clone());
			let tail = verify(
				metacontext,
				&context.clone().extend(assignee.clone(), argument_ty_value, argument_value),
				*tail,
				ty,
			)?;
			Some(Term::Let { assignee, ty: bx!(argument_ty), argument: bx!(argument), tail: bx!(tail) })
		}
		(Preterm::Hole, _) => Some(Term::InsertedMetavariable {
			metavariable: metacontext.spawn(),
			is_abstract: context.is_abstract.clone(),
		}),
		(term, _) => {
			let (term, synthesized_ty) = synthesize(metacontext, context, term)?;
			if metacontext.unify(context.len(), synthesized_ty, ty) {
				Some(term)
			} else {
				None
			}
		}
	}
}

pub fn synthesize(
	metacontext: &mut Metacontext,
	context: &Context,
	term: Preterm,
) -> Option<(Term, Rc<Value>)> {
	match term {
		Preterm::Hole => {
			let ty = evaluate(context.environment.clone(), Term::Metavariable(metacontext.spawn()));
			Some((Term::Metavariable(metacontext.spawn()), ty))
		}
		Preterm::Variable(name) => context.tys.iter().rev().enumerate().find_map(|(i, (name_1, ty))| {
			if &name == name_1 {
				Some((Term::Variable(Index(i)), ty.clone()))
			} else {
				None
			}
		}),
		Preterm::Pair { .. } => None, // TODO: infer non-dependent pair?
		Preterm::Lambda { .. } => todo!(), // We can infer a lambda by introducing a metavariable for its domain.
		Preterm::Compute { scrutinee, eliminators: raw_eliminators } => {
			let (scrutinee, mut total_ty) = synthesize(metacontext, context, *scrutinee)?;
			let mut eliminators = vec![];
			for raw_eliminator in raw_eliminators {
				match raw_eliminator {
					RawEliminator::Apply { argument } => {
						// TODO: force total_ty before proceeding (should probably do this at the start of each iteration).
						if let Value::Pi { parameter: _, base, family } = total_ty.as_ref() {
							let argument = verify(metacontext, context, argument, base.clone())?;
							let argument_value = evaluate(context.environment.clone(), argument.clone());
							eliminators.push(Eliminator::Apply { argument });
							total_ty = family.clone().apply_value(argument_value);
						} else {
							// TODO: try introducing metas for the base and family and unify pi with metas with total_ty.
							return None;
						}
					}
					RawEliminator::ProjectBase => {
						if let Value::Sigma { parameter: _, base, family: _ } = total_ty.as_ref() {
							eliminators.push(Eliminator::ProjectBase);
							total_ty = base.clone();
						} else {
							return None;
						}
					}
					RawEliminator::ProjectFiber => {
						if let Value::Sigma { parameter: _, base: _, family } = total_ty.as_ref() {
							let basepoint_value = {
								let mut eliminators = eliminators.clone();
								eliminators.push(Eliminator::ProjectBase);
								evaluate(
									context.environment.clone(),
									Term::Compute { scrutinee: bx!(scrutinee.clone()), eliminators },
								)
							};
							eliminators.push(Eliminator::ProjectFiber);
							total_ty = family.clone().apply_value(basepoint_value);
						} else {
							return None;
						}
					}
				}
			}
			Some((Term::Compute { scrutinee: bx!(scrutinee), eliminators }, total_ty))
		}
		Preterm::Universe => Some((Term::Universe, rc!(Value::Universe))),
		Preterm::Pi { parameter, base, family } => {
			let base = verify(metacontext, context, *base, rc!(Value::Universe))?;
			let base_value = evaluate(context.environment.clone(), base.clone());
			let family = verify(
				metacontext,
				&context.clone().bind(parameter.clone(), base_value),
				*family,
				rc!(Value::Universe),
			)?;
			Some((Term::Pi { parameter, base: bx!(base), family: bx!(family) }, rc!(Value::Universe)))
		}
		Preterm::Sigma { parameter, base, family } => {
			let base = verify(metacontext, context, *base, rc!(Value::Universe))?;
			let base_value = evaluate(context.environment.clone(), base.clone());
			let family = verify(
				metacontext,
				&context.clone().bind(parameter.clone(), base_value),
				*family,
				rc!(Value::Universe),
			)?;
			Some((Term::Sigma { parameter, base: bx!(base), family: bx!(family) }, rc!(Value::Universe)))
		}
		Preterm::Let { assignee, ty: argument_ty, argument, tail } => {
			let argument_ty = verify(metacontext, context, *argument_ty, rc!(Value::Universe))?;
			let argument_ty_value = evaluate(context.environment.clone(), argument_ty.clone());
			let argument = verify(metacontext, context, *argument, argument_ty_value.clone())?;
			let argument_value = evaluate(context.environment.clone(), argument.clone());
			let (tail, tail_ty) = synthesize(
				metacontext,
				&context.clone().extend(assignee.clone(), argument_ty_value, argument_value),
				*tail,
			)?;
			Some((
				Term::Let { assignee, ty: bx!(argument_ty), argument: bx!(argument), tail: bx!(tail) },
				tail_ty,
			))
		}
	}
}
