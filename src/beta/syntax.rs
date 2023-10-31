use bitvec::vec::BitVec;

use super::common::{Index, Metavariable, Name};

#[derive(Clone, Debug)]
pub enum Eliminator {
	Apply { argument: Term },
	ProjectBase,
	ProjectFiber,
}

// The core syntax: the output of the elaborator.
#[derive(Clone, Debug)]
pub enum Term {
	Variable(Index),
	Lambda { parameter: Name, body: Box<Self> },
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	Compute { scrutinee: Box<Self>, eliminators: Vec<Eliminator> },
	Universe,
	Pi { parameter: Name, base: Box<Self>, family: Box<Self> },
	Sigma { parameter: Name, base: Box<Self>, family: Box<Self> },
	Let { assignee: Name, ty: Box<Self>, argument: Box<Self>, tail: Box<Self> },
	Metavariable(Metavariable),
	InsertedMetavariable { metavariable: Metavariable, is_abstract: BitVec }, // abstract variables in scopes are passed as "arguments" to the metavariable.
}
