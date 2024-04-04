use crate::delta::common::{Binder, Cost, Cpy, Field, Index, Name, Repr, ReprAtom};

#[derive(Clone, Debug)]
pub enum StaticTerm {
	// Variables.
	Variable(Option<Name>, Index),

	// Let-expressions.
	Let {
		grade: Cost,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},

	// Types.
	Universe(Cpy),

	// Universe indices.
	Cpy,
	CpyNt,
	CpyMax(Vec<Self>),

	Repr,
	ReprAtom(Option<ReprAtom>),
	ReprExp(usize, Box<Self>),
	ReprPair(Box<Self>, Box<Self>),

	// Quoted programs.
	Lift {
		liftee: Box<DynamicTerm>,
		kind: Box<KindTerm>,
	},
	Quote(Box<DynamicTerm>),

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
		base_copy: Cpy,
		base: Box<Self>,
		family: Binder<Box<Self>>,
	},
	Function(usize, Binder<Box<Self>>),
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},

	// Dependent pairs.
	Sg {
		base_copy: Cpy,
		base: Box<Self>,
		family_copy: Cpy,
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
	SgField(Box<Self>, Field),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		cases: Vec<Self>,
	},

	// Natural numbers.
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
	},
}

#[derive(Clone, Debug)]
pub enum DynamicTerm {
	// Variables.
	Variable(Option<Name>, Index),

	// Let-expressions.
	Def {
		grade: Cost,
		ty: Box<StaticTerm>,
		argument: Box<StaticTerm>,
		tail: Binder<Box<Self>>,
	},
	Let {
		grade: usize,
		ty: Box<Self>,
		argument_kind: Box<KindTerm>,
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
		domain_kind: Option<Box<KindTerm>>,
		codomain_kind: Option<Box<KindTerm>>,
		body: Binder<Box<Self>>,
	},
	Apply {
		scrutinee: Box<Self>,
		// TODO: None doesn't mean Inf here, but irrelevance. Use Cost where applicable (i.e. during elaboration, not here) to avoid confusion.
		grade: Option<usize>,
		argument: Box<Self>,
		family_kind: Option<Box<KindTerm>>,
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
		kinds: [Box<KindTerm>; 2],
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
		motive_kind: Option<Box<KindTerm>>,
		motive: Binder<Box<Self>>,
		cases: Vec<Self>,
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

	// Natural numbers.
	Nat,
	Num(usize),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive_kind: Option<Box<KindTerm>>,
		motive: Binder<Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Box<Self>, 2>,
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

#[derive(Clone, Debug)]
pub struct KindTerm {
	pub copy: StaticTerm,
	pub repr: StaticTerm,
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
