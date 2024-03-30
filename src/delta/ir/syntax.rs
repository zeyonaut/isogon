use crate::delta::common::{Binder, Copyability, Field, Index, Name, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Option<Name>, Index),
	
	Let { 
		grade: usize, ty: Box<Self>, argument: Box<Self>, tail: Binder<Box<Self>> },

	Universe,

	Lift { liftee: Box<DynamicTerm>, copy: Box<Self>, repr: Box<Self> },
	Quote(Box<DynamicTerm>),

	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp { grade: usize, argument: Box<Self>, tail: Binder<Box<Self>>},

	Pi(usize, Box<Self>, Binder<Box<Self>>),
	Lambda(usize, Binder<Box<Self>>),
	Apply { scrutinee: Box<Self>, argument: Box<Self> },

	CopyabilityType,
	Copyability(Copyability),
	MaxCopyability(Box<Self>, Box<Self>),

	ReprType,
	ReprAtom(Option<ReprAtom>),
	ReprExp(usize, Box<Self>)
}

impl From<&Repr> for StaticTerm {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(Some(*atom)),
		}
	}
}

impl From<Option<&Repr>> for StaticTerm {
	fn from(value: Option<&Repr>) -> Self {
		match value {
			Some(repr) => repr.into(),
			None => Self::ReprAtom(None),
		}
	}
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	Variable(Option<Name>, Index),

	Let {
		grade: usize,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},

	Universe {
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},

	Splice(Box<StaticTerm>),

	Pi {
		grade: usize,
		base_copyability: Box<StaticTerm>,
		base_representation: Box<StaticTerm>,
		base: Box<Self>,
		family_copyability: Box<StaticTerm>,
		family_representation: Box<StaticTerm>,
		family: Binder<Box<Self>>,
	},
	Function {
		grade: usize,
		base: Box<Self>,
		family: Binder<Box<Self>>,
		body: Binder<Box<Self>>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
		fiber_copyability: Box<StaticTerm>,
		fiber_representation: Box<StaticTerm>,
		base: Box<Self>,
		family: Binder<Box<Self>>,
	},
	
	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp { grade: usize, argument: Box<Self>, tail: Binder<Box<Self>>},
}
