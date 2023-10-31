use std::rc::Rc;

use super::{
	common::{Index, Metavariable, Name},
	syntax::{self, Term},
};
use crate::utility::rc;

// de Bruijn level: zero is the oldest bound parameter.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Level(pub(super) usize);

impl Level {
	pub fn suc(self) -> Self {
		let Self(level) = self;
		Self(level + 1)
	}
}

pub type Environment = Vec<Rc<Value>>;

#[derive(Clone, Debug)]
pub struct Closure(pub Environment, pub Term);

impl Closure {
	pub fn apply_value(self, argument: Rc<Value>) -> Rc<Value> {
		let Self(environment, body) = self;
		let mut environment = environment.clone();
		environment.push(argument);
		evaluate(environment, body)
	}
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Head {
	Variable(Level),
	Metavariable(Metavariable),
}

#[derive(Clone, Debug)]
pub enum NeutralEliminator {
	Apply { argument: Rc<Value> },
	ProjectBase,
	ProjectFiber,
}

// The semantic domain (of values).
#[derive(Clone, Debug)]
pub enum Value {
	// A neutral form.
	Neutral { head: Head, eliminators: Vec<NeutralEliminator> },
	Lambda { parameter: Name, body: Closure },
	Pair { basepoint: Rc<Self>, fiberpoint: Rc<Self> },
	Pi { parameter: Name, base: Rc<Self>, family: Closure },
	Sigma { parameter: Name, base: Rc<Self>, family: Closure },
	Universe,
}

impl Value {
	pub fn variable(variable: Level) -> Self {
		Self::Neutral { head: Head::Variable(variable), eliminators: vec![] }
	}

	pub fn eliminate(self, eliminator: NeutralEliminator) -> Rc<Self> {
		match self {
			Self::Neutral { head, mut eliminators } => {
				eliminators.push(eliminator);
				rc!(Self::Neutral { head, eliminators })
			}
			Self::Lambda { parameter, body } => {
				let NeutralEliminator::Apply { argument } = eliminator else { panic!("bad eliminator") };
				body.apply_value(argument)
			}
			Self::Pair { basepoint, fiberpoint } => match eliminator {
				NeutralEliminator::ProjectBase => basepoint,
				NeutralEliminator::ProjectFiber => fiberpoint,
				_ => panic!("bad eliminator"),
			},
			_ => panic!("bad eliminator"),
		}
	}
}

// Evaluation: Take an environment and a term, and produce a value.
// Precondition: Since term is a core term, it must be well-typed (and so must environment).
pub fn evaluate(environment: Environment, term: Term) -> Rc<Value> {
	use Term::*;
	match term {
		Metavariable(..) => todo!(),
		InsertedMetavariable { .. } => todo!(),
		Variable(Index(index)) => environment[environment.len() - 1 - index].clone(),
		Lambda { parameter, body } =>
			rc!(Value::Lambda { parameter, body: Closure(environment.clone(), *body) }),
		Pair { basepoint, fiberpoint } => rc!(Value::Pair {
			basepoint: evaluate(environment.clone(), *basepoint),
			fiberpoint: evaluate(environment, *fiberpoint)
		}),
		Compute { scrutinee, eliminators } => {
			let mut scrutinee = evaluate(environment.clone(), *scrutinee);

			for eliminator in eliminators {
				match eliminator {
					syntax::Eliminator::Apply { argument } => {
						let argument = evaluate(environment.clone(), argument); // Note: an unnecessary clone is made here at the end of the loop.
						if let Value::Lambda { parameter: _, body } = scrutinee.as_ref() {
							scrutinee = body.clone().apply_value(argument)
						} else if let Value::Neutral { head: Head::Variable(variable), eliminators } =
							scrutinee.as_ref()
						{
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::Apply { argument });
							scrutinee = rc!(Value::Neutral { head: Head::Variable(*variable), eliminators })
						} else {
							panic!();
						}
					}
					syntax::Eliminator::ProjectBase =>
						if let Value::Pair { basepoint, .. } = scrutinee.as_ref() {
							scrutinee = basepoint.clone();
						} else if let Value::Neutral { head: Head::Variable(variable), eliminators } =
							scrutinee.as_ref()
						{
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::ProjectBase);
							scrutinee = rc!(Value::Neutral { head: Head::Variable(*variable), eliminators })
						} else {
							panic!();
						},
					syntax::Eliminator::ProjectFiber =>
						if let Value::Pair { fiberpoint, .. } = scrutinee.as_ref() {
							scrutinee = fiberpoint.clone();
						} else if let Value::Neutral { head: Head::Variable(variable), eliminators } =
							scrutinee.as_ref()
						{
							let mut eliminators = eliminators.clone();
							eliminators.push(NeutralEliminator::ProjectFiber);
							scrutinee = rc!(Value::Neutral { head: Head::Variable(*variable), eliminators })
						} else {
							panic!();
						},
				}
			}

			scrutinee
		}
		Universe => rc!(Value::Universe),
		Pi { parameter, base, family } => rc!(Value::Pi {
			parameter,
			base: evaluate(environment.clone(), *base),
			family: Closure(environment, *family),
		}),
		Sigma { parameter, base, family } => rc!(Value::Sigma {
			parameter,
			base: evaluate(environment.clone(), *base),
			family: Closure(environment, *family),
		}),
		Let { assignee: _, ty: _, argument, tail } => {
			let argument = evaluate(environment.clone(), *argument);
			let mut environment = environment.clone();
			environment.push(argument);
			evaluate(environment, *tail)
		}
	}
}
