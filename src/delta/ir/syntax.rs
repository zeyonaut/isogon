use crate::delta::common::{Binder, Cpy, Field, Index, Name, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub struct KindTerm {
	pub copy: StaticTerm,
	pub repr: StaticTerm,
}

#[derive(Clone, Debug)]
pub enum StaticTerm {
	// Variables.
	Variable(Option<Name>, Index),

	// Let-expressions.
	Let { grade: usize, ty: Box<Self>, argument: Box<Self>, tail: Binder<Box<Self>> },

	// Types.
	Universe,

	// Universe indices.
	Cpy,
	CpyValue(Cpy),
	CpyMax(Box<Self>, Box<Self>),

	Repr,
	ReprAtom(Option<ReprAtom>),
	ReprExp(usize, Box<Self>),
	ReprPair(Box<Self>, Box<Self>),

	// Quoted programs.
	Lift { liftee: Box<DynamicTerm>, kind: Box<KindTerm> },
	Quote(Box<DynamicTerm>),

	// Repeated programs.
	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp { grade: usize, grade_argument: usize, argument: Box<Self>, tail: Binder<Box<Self>> },

	// Dependent functions.
	Pi(usize, Box<Self>, Binder<Box<Self>>),
	Function(usize, Binder<Box<Self>>),
	Apply { scrutinee: Box<Self>, argument: Box<Self> },

	// Dependent pairs.
	Sg(Box<Self>, Binder<Box<Self>>),
	Pair { basepoint: Box<Self>, fiberpoint: Box<Self> },
	SgLet { grade: usize, argument: Box<Self>, tail: Binder<Box<Self>, 2> },
	SgField(Box<Self>, Field),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum { scrutinee: Box<Self>, motive: Binder<Box<Self>>, cases: Vec<Self> },
}

impl From<&Repr> for StaticTerm {
	fn from(value: &Repr) -> Self {
		match value {
			Repr::Atom(atom) => Self::ReprAtom(Some(*atom)),
			Repr::Pair(l, r) => Self::ReprPair(Self::from(&**l).into(), Self::from(&**r).into()),
			Repr::Exp(n, r) => Self::ReprExp(*n, Self::from(&**r).into()),
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
	// Variables.
	Variable(Option<Name>, Index),

	// Let-expressions.
	Let {
		grade: usize,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},

	// Types.
	Universe {
		kind: Box<KindTerm>,
	},

	// Quoted programs.
	Splice(Box<StaticTerm>),

	// Repeated programs.
	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp {
		grade: usize,
		grade_argument: usize,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},

	// Dependent functions.
	Pi {
		grade: usize,
		base_kind: Box<KindTerm>,
		base: Box<Self>,
		family_kind: Box<KindTerm>,
		family: Binder<Box<Self>>,
	},
	Function {
		grade: usize,
		body: Binder<Box<Self>>,
		base: Option<Box<Self>>,
		family: Option<Binder<Box<Self>>>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
		base: Option<Box<Self>>,
		family_kind: Option<Box<KindTerm>>,
		family: Option<Binder<Box<Self>>>,
	},

	// Dependent pairs.
	Sg {
		base_kind: Box<KindTerm>,
		base: Box<Self>,
		family_kind: Box<KindTerm>,
		family: Binder<Box<Self>>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	SgLet {
		grade: usize,
		argument: Box<Self>,
		tail: Binder<Box<Self>, 2>,
	},
	SgField {
		scrutinee: Box<Self>,
		field: Field,
	},

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		cases: Vec<Self>,
		motive: Binder<Box<Self>>,
		motive_kind: Option<Box<KindTerm>>,
	},

	// Paths.
	Id {
		kind: Box<KindTerm>,
		space: Box<Self>,
		left: Box<Self>,
		right: Box<Self>,
	},
	Refl,
	CasePath {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>, 2>,
		case_refl: Box<Self>,
	},

	// Wrappers.
	Bx {
		kind: Box<KindTerm>,
		inner: Box<Self>,
	},
	BxValue(Box<Self>),
	BxProject {
		kind: Option<Box<KindTerm>>,
		scrutinee: Box<Self>,
	},
	Wrap {
		kind: Box<KindTerm>,
		inner: Box<Self>,
	},
	WrapValue(Box<Self>),
	WrapProject {
		kind: Option<Box<KindTerm>>,
		scrutinee: Box<Self>,
	},
}
