use crate::gamma::common::{Binder, Copyability, Field, Index, Name, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	Variable(Option<Name>, Index),
	Let {
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},
	Lift {
		liftee: Box<DynamicTerm>,
		copy: Box<Self>,
		repr: Box<Self>,
	},
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
	Project(Box<Self>, Field),
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		cases: Vec<Self>,
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
	WrapType {
		inner: Box<Self>,
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
	WrapNew(Box<Self>),
	Unwrap {
		scrutinee: Box<Self>,
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
	RcType {
		inner: Box<Self>,
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
	RcNew(Box<Self>),
	UnRc {
		scrutinee: Box<Self>,
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},
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
		fiber_copyability: Box<StaticTerm>,
		fiber_representation: Box<StaticTerm>,
		base: Box<Self>,
		family: Binder<Box<Self>>,
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
	Project {
		scrutinee: Box<Self>,
		projection: Field,
		projection_copyability: Box<StaticTerm>,
		projection_representation: Box<StaticTerm>,
	},
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
		fiber_copyability: Box<StaticTerm>,
		fiber_representation: Box<StaticTerm>,
		motive: Binder<Box<Self>>,
	},
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		cases: Vec<Self>,
		fiber_copyability: Box<StaticTerm>,
		fiber_representation: Box<StaticTerm>,
		motive: Binder<Box<Self>>,
	},
}
