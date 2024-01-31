use crate::gamma::common::{Binder, Copyability, Index, Name, Projection, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Name, Index),
	Let {
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Lift(Box<DynamicTerm>),
	Quote(Box<DynamicTerm>),
	Universe,
	Pi(Box<Self>, Binder<Box<Self>>),
	Lambda(Binder<Box<Self>>),
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma(Box<Self>, Binder<Box<Self>>),
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
	CopyabilityType,
	Copyability(Copyability),
	MaxCopyability(Box<Self>, Box<Self>),
	ReprType,
	ReprAtom(Option<ReprAtom>),
	ReprPair(Box<Self>, Box<Self>),
	ReprMax(Box<Self>, Box<Self>),
	ReprUniv(Box<Self>),
}

impl From<&Repr> for StaticTerm {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(Some(*atom)),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Max(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
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
	Variable(Name, Index),
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
	WrapType(Box<Self>),
	WrapNew(Box<Self>),
	Unwrap(Box<Self>),
	RcType(Box<Self>),
	RcNew(Box<Self>),
	UnRc(Box<Self>),
	// NOTE: C and R are terms, but it's unclear to me if they are better represented as values but with de Bruijn indices.
	Pi {
		base_copyability: Box<StaticTerm>,
		base_representation: Box<StaticTerm>,
		base: Box<Self>,
		family_copyability: Box<StaticTerm>,
		family_representation: Box<StaticTerm>,
		family: Binder<Box<Self>>,
	},
	Lambda {
		base: Box<Self>,
		family: Binder<Box<Self>>,
		body: Binder<Box<Self>>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		base_copyability: Box<StaticTerm>,
		base_representation: Box<StaticTerm>,
		base: Box<Self>,
		family_copyability: Box<StaticTerm>,
		family_representation: Box<StaticTerm>,
		family: Binder<Box<Self>>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	Project(Box<Self>, Projection),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Bool,
	BoolValue(bool),
	CaseBool {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_false: Box<Self>,
		case_true: Box<Self>,
	},
}
