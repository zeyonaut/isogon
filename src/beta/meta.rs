use std::rc::Rc;

use super::{
	common::{Index, Metavariable},
	domain::{Level, NeutralEliminator, Value},
	syntax::Term,
};
use crate::{
	beta::{domain::Head, syntax::Eliminator},
	utility::{bx, rc},
};

pub struct Metacontext {
	entries: Vec<Option<Rc<Value>>>,
}

impl Metacontext {
	pub fn new() -> Self {
		Self { entries: Vec::new() }
	}

	pub fn spawn(&mut self) -> Metavariable {
		let metavariable = self.entries.len();
		self.entries.push(None);
		Metavariable(metavariable)
	}

	pub fn unify_eliminators(
		&mut self,
		context_length: Level,
		left: &[NeutralEliminator],
		right: &[NeutralEliminator],
	) -> bool {
		for eliminator_pair in left.iter().zip(right.iter()) {
			match eliminator_pair {
				(
					NeutralEliminator::Apply { argument: left_argument },
					NeutralEliminator::Apply { argument: right_argument },
				) =>
					if !self.unify(context_length, left_argument.clone(), right_argument.clone()) {
						return false;
					},
				(NeutralEliminator::ProjectBase, NeutralEliminator::ProjectBase) => {}
				(NeutralEliminator::ProjectFiber, NeutralEliminator::ProjectFiber) => {}
				_ => return false,
			}
		}
		return true;
	}

	pub fn unify(&mut self, context_length: Level, left: Rc<Value>, right: Rc<Value>) -> bool {
		use Value::*;
		match (left.as_ref(), right.as_ref()) {
			(Universe, Universe) => true,
			(
				Pi { parameter: _, base: left_base, family: left_family },
				Pi { parameter: _, base: right_base, family: right_family },
			) =>
				self.unify(context_length, left_base.clone(), right_base.clone())
					&& self.unify(
						context_length.suc(),
						left_family.clone().apply_value(rc!(Value::variable(context_length))),
						right_family.clone().apply_value(rc!(Value::variable(context_length))),
					),
			(
				Sigma { parameter: _, base: left_base, family: left_family },
				Sigma { parameter: _, base: right_base, family: right_family },
			) =>
				self.unify(context_length, left_base.clone(), right_base.clone())
					&& self.unify(
						context_length.suc(),
						left_family.clone().apply_value(rc!(Value::variable(context_length))),
						right_family.clone().apply_value(rc!(Value::variable(context_length))),
					),
			(Lambda { parameter: _, body: left_body }, Lambda { parameter: _, body: right_body }) => self.unify(
				context_length.suc(),
				left_body.clone().apply_value(rc!(Value::variable(context_length))),
				right_body.clone().apply_value(rc!(Value::variable(context_length))),
			),
			(Lambda { parameter: _, body: left_body }, Neutral { head, eliminators }) => self.unify(
				context_length.suc(),
				left_body.clone().apply_value(rc!(Value::variable(context_length))),
				rc!({
					let mut eliminators = eliminators.clone();
					eliminators.push(NeutralEliminator::Apply { argument: rc!(Value::variable(context_length)) });
					Neutral { head: *head, eliminators }
				}),
			),
			(Neutral { head, eliminators }, Lambda { parameter: _, body: right_body }) => self.unify(
				context_length.suc(),
				rc!({
					let mut eliminators = eliminators.clone();
					eliminators.push(NeutralEliminator::Apply { argument: rc!(Value::variable(context_length)) });
					Neutral { head: *head, eliminators }
				}),
				right_body.clone().apply_value(rc!(Value::variable(context_length))),
			),
			(
				Pair { basepoint: left_basepoint, fiberpoint: left_fiberpoint },
				Pair { basepoint: right_basepoint, fiberpoint: right_fiberpoint },
			) =>
				self.unify(context_length, left_basepoint.clone(), right_basepoint.clone())
					&& self.unify(context_length, left_fiberpoint.clone(), right_fiberpoint.clone()),
			(Pair { basepoint: left_basepoint, fiberpoint: left_fiberpoint }, Neutral { head, eliminators }) => {
				let mut eliminators_basepoint = eliminators.clone();
				eliminators_basepoint.push(NeutralEliminator::ProjectBase);
				let mut eliminators_fiberpoint = eliminators.clone();
				eliminators_fiberpoint.push(NeutralEliminator::ProjectFiber);
				self.unify(
					context_length,
					left_basepoint.clone(),
					rc!(Neutral { head: *head, eliminators: eliminators_basepoint }),
				) && self.unify(
					context_length,
					left_fiberpoint.clone(),
					rc!(Neutral { head: *head, eliminators: eliminators_fiberpoint }),
				)
			}
			(
				Neutral { head, eliminators },
				Pair { basepoint: right_basepoint, fiberpoint: right_fiberpoint },
			) => {
				let mut eliminators_basepoint = eliminators.clone();
				eliminators_basepoint.push(NeutralEliminator::ProjectBase);
				let mut eliminators_fiberpoint = eliminators.clone();
				eliminators_fiberpoint.push(NeutralEliminator::ProjectFiber);
				self.unify(
					context_length,
					rc!(Neutral { head: *head, eliminators: eliminators_basepoint }),
					right_basepoint.clone(),
				) && self.unify(
					context_length,
					rc!(Neutral { head: *head, eliminators: eliminators_fiberpoint }),
					right_fiberpoint.clone(),
				)
			}
			(
				Neutral { head: left_head, eliminators: left_eliminators },
				Neutral { head: right_head, eliminators: right_eliminators },
			) if left_head == right_head =>
				self.unify_eliminators(context_length, &left_eliminators, &right_eliminators),
			(
				Neutral { head: Head::Metavariable(metavariable), eliminators: metavariable_eliminators },
				target,
			) => self.solve(context_length, *metavariable, metavariable_eliminators, target),
			(
				target,
				Neutral { head: Head::Metavariable(metavariable), eliminators: metavariable_eliminators },
			) => self.solve(context_length, *metavariable, metavariable_eliminators, target),
			_ => false,
		}
	}

	// Solve a metavariable equation.
	// TODO: don't panic.
	pub fn solve(
		&mut self,
		context_length: Level,
		definee: Metavariable,
		eliminators: &[NeutralEliminator],
		target: &Value,
	) -> bool {
		// This partial renaming maps variables in the context to positions in the spine, 0 being leftmost.
		let partial_renaming = {
			let mut partial_renaming = Vec::new();
			partial_renaming.resize(context_length.0, None);
			for (i, eliminator) in eliminators.into_iter().enumerate() {
				// We only consider spines consisting of applications to variables.
				let NeutralEliminator::Apply { argument } = eliminator else {
					panic!("attempted to solve metavariable equation with non-application eliminators");
				};
				let Value::Neutral { head: Head::Variable(variable), eliminators } =
					self.force(argument.as_ref().clone())
				else {
					panic!("attempted to solve metavariable equation with non-variable application");
				};
				if !eliminators.is_empty() {
					panic!("attempted to solve metavariable equation with non-variable application");
				}
				// We only consider spines which mention each variable at most once to ensure a unique unifier.
				if partial_renaming[variable.0].is_some() {
					panic!("metavariable spine mentions a variable multiple times");
				}
				partial_renaming[variable.0] = Some(Level(i));
			}
			PartialRenaming::new(eliminators.len(), partial_renaming)
		};

		let renamed_target = self.rename(definee, &partial_renaming, 0, target.clone());

		todo!();
		false
	}

	// Apply a partial renaming to a value while quoting it and ensure that a given metavariable is not named within.
	pub fn rename(
		&self,
		definee: Metavariable,
		partial_renaming: &PartialRenaming,
		additional_bindings: usize,
		value: Value,
	) -> Term {
		match self.force(value) {
			Value::Neutral { head: Head::Metavariable(hole), eliminators } =>
				if hole == definee {
					panic!("metavariable equation yields an impredicative solution");
				} else {
					let head = Term::Metavariable(hole);
					let mut spine = Vec::new();

					for eliminator in eliminators {
						match eliminator {
							NeutralEliminator::Apply { argument } => spine.push(Eliminator::Apply {
								argument: self.rename(
									definee,
									partial_renaming,
									additional_bindings,
									argument.as_ref().clone(),
								),
							}),
							NeutralEliminator::ProjectBase => spine.push(Eliminator::ProjectBase),
							NeutralEliminator::ProjectFiber => spine.push(Eliminator::ProjectFiber),
						}
					}

					if spine.is_empty() {
						head
					} else {
						Term::Compute { scrutinee: bx!(head), eliminators: spine }
					}
				},
			Value::Neutral { head: Head::Variable(variable), eliminators } => {
				let Some(renamed_index) = partial_renaming.get_renamed_index(variable, additional_bindings)
				else {
					panic!("variable not in renaming") // TODO: when, exactly, does this happen?
				};

				let head = Term::Variable(renamed_index);
				let mut spine = Vec::new();

				for eliminator in eliminators {
					match eliminator {
						NeutralEliminator::Apply { argument } => spine.push(Eliminator::Apply {
							argument: self.rename(
								definee,
								partial_renaming,
								additional_bindings,
								argument.as_ref().clone(),
							),
						}),
						NeutralEliminator::ProjectBase => spine.push(Eliminator::ProjectBase),
						NeutralEliminator::ProjectFiber => spine.push(Eliminator::ProjectFiber),
					}
				}

				if spine.is_empty() {
					head
				} else {
					Term::Compute { scrutinee: bx!(head), eliminators: spine }
				}
			}
			Value::Lambda { parameter, body } => Term::Lambda {
				parameter,
				body: bx!(self.rename(
					definee,
					partial_renaming,
					additional_bindings + 1,
					body
						.apply_value(rc!(Value::variable(Level(partial_renaming.hole_arity + additional_bindings))))
						.as_ref()
						.clone()
				)),
			},
			Value::Pair { basepoint, fiberpoint } => Term::Pair {
				basepoint: bx!(self.rename(
					definee,
					partial_renaming,
					additional_bindings,
					basepoint.as_ref().clone()
				)),
				fiberpoint: bx!(self.rename(
					definee,
					partial_renaming,
					additional_bindings,
					fiberpoint.as_ref().clone()
				)),
			},
			Value::Pi { parameter, base, family } => Term::Pi {
				parameter,
				base: bx!(self.rename(definee, partial_renaming, additional_bindings, base.as_ref().clone())),
				family: bx!(self.rename(
					definee,
					partial_renaming,
					additional_bindings + 1,
					family
						.apply_value(rc!(Value::variable(Level(partial_renaming.hole_arity + additional_bindings))))
						.as_ref()
						.clone()
				)),
			},
			Value::Sigma { parameter, base, family } => Term::Sigma {
				parameter,
				base: bx!(self.rename(definee, partial_renaming, additional_bindings, base.as_ref().clone())),
				family: bx!(self.rename(
					definee,
					partial_renaming,
					additional_bindings + 1,
					family
						.apply_value(rc!(Value::variable(Level(partial_renaming.hole_arity + additional_bindings))))
						.as_ref()
						.clone()
				)),
			},
			Value::Universe => Term::Universe,
		}
	}

	// (Non-recursively) unfold a solved flex neutral form by replacing its head with its solution.
	pub fn force(&self, value: Value) -> Value {
		match value {
			Value::Neutral { head: Head::Metavariable(metavariable), eliminators } => {
				let Some(term) = &self[metavariable] else {
					return Value::Neutral { head: Head::Metavariable(metavariable), eliminators };
				};

				//self.force(term.as_ref().clone().eliminate_spine(eliminators.into_iter()).as_ref().clone())
				//TODO: Check if this is good.
				todo!()
			}
			value => value,
		}
	}
}

impl std::ops::Index<Metavariable> for Metacontext {
	type Output = Option<Rc<Value>>;

	fn index(&self, Metavariable(index): Metavariable) -> &Self::Output {
		&self.entries[index]
	}
}

pub struct PartialRenaming {
	hole_arity: usize,
	partial_renaming: Vec<Option<Level>>,
}

impl PartialRenaming {
	pub fn new(hole_arity: usize, partial_renaming: Vec<Option<Level>>) -> Self {
		Self { hole_arity, partial_renaming }
	}

	pub fn get_renamed_index(&self, Level(level): Level, additional_bindings: usize) -> Option<Index> {
		if let Some(renamed_level) = self.partial_renaming.get(level) {
			let Level(renamed_level) = (*renamed_level)?;
			Some(Index(additional_bindings + (self.hole_arity - 1 - renamed_level)))
		} else {
			let relative_level = level - self.partial_renaming.len();
			if relative_level < additional_bindings {
				Some(Index(additional_bindings - 1 - relative_level))
			} else {
				None
			}
		}
	}
}
