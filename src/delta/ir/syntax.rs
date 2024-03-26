use crate::delta::common::{Binder, Copyability, Field, Index, Name, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Option<Name>, Index),
	Let { ty: Box<Self>, argument: Box<Self>, tail: Binder<Box<Self>> },
	Lift { liftee: Box<DynamicTerm>, copy: Box<Self>, repr: Box<Self> },
	Quote(Box<DynamicTerm>),
	Universe,
	Pi(Option<usize>, Box<Self>, Binder<Box<Self>>),
	Lambda(Binder<Box<Self>>),
	Apply { scrutinee: Box<Self>, argument: Box<Self> },
	CopyabilityType,
	Copyability(Copyability),
	MaxCopyability(Box<Self>, Box<Self>),
	ReprType,
	ReprAtom(Option<ReprAtom>),
	ReprUniv(Box<Self>),
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
		// Type of the assignee.
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Splice(Box<StaticTerm>),
	Universe {
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
	// NOTE: C and R are terms, but it's unclear to me if they are better represented as values but with de Bruijn indices.
	Pi {
		grade: Option<usize>,
		base_copyability: Box<StaticTerm>,
		base_representation: Box<StaticTerm>,
		base: Box<Self>,
		family_copyability: Box<StaticTerm>,
		family_representation: Box<StaticTerm>,
		family: Binder<Box<Self>>,
	},
	Function {
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
}
