use crate::{
	common::{ArraySize, Binder, Cost, Cpy, Field, Fragment, Index, Label, Name, Repr, ReprAtom},
	ir::semantics::{DynamicValue, KindValue},
};

#[derive(Clone)]
pub struct CoreProgram {
	pub input: Option<(Label, KindValue)>,
	pub term: DynamicTerm,
	pub ty: DynamicValue,
	pub kind: KindValue,
}

#[derive(Clone, Debug)]
pub enum StaticTerm {
	// Variables.
	Variable(Option<Name>, Index),

	// Let-expressions.
	Let {
		grade: Cost,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>>,
	},

	// Types.
	Universe(Cpy),

	// Universe indices.
	Cpy,
	CpyNt,
	CpyMax(Vec<Self>),

	Repr,
	ReprAtom(Option<ReprAtom>),
	ReprExp {
		len: ArraySize,
		kind: Box<KindTerm>,
	},
	ReprPair(Box<Self>, Box<Self>),

	// Quoted programs.
	Lift {
		liftee: Box<DynamicTerm>,
		kind: Box<KindTerm>,
	},
	Quote(Box<DynamicTerm>),

	// Repeated programs.
	Exp(Cost, Cpy, Box<Self>),
	Repeat(Cost, Box<Self>),
	ExpLet {
		grade: Cost,
		grade_argument: Cost,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>>,
	},
	ExpProject(Box<Self>),

	// Dependent functions.
	Pi {
		fragment: Fragment,
		base_copy: Cpy,
		base: Box<Self>,
		family_copy: Cpy,
		family: Binder<Label, Box<Self>>,
	},
	Function(Fragment, Binder<Label, Box<Self>>),
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},

	// Dependent pairs.
	Sg {
		base_copy: Cpy,
		base: Box<Self>,
		family_copy: Cpy,
		family: Binder<Label, Box<Self>>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	SgLet {
		grade: Cost,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>, 2>,
	},
	SgField(Box<Self>, Field),

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		motive: Binder<Label, Box<Self>>,
		cases: Vec<Self>,
	},

	// Natural numbers.
	Nat,
	Num(u64),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive: Binder<Label, Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Label, Box<Self>, 2>,
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
		tail: Binder<Label, Box<Self>>,
	},
	Let {
		grade: u64,
		ty: Box<Self>,
		argument_kind: Box<KindTerm>,
		argument: Box<Self>,
		tail: Binder<Label, Box<Self>>,
	},

	// Types.
	Universe {
		kind: Box<KindTerm>,
	},

	// Quoted programs.
	Splice(Box<StaticTerm>),

	// Repeated programs.
	Exp(u64, Box<KindTerm>, Box<Self>),
	Repeat {
		grade: u64,
		kind: Option<Box<KindTerm>>,
		term: Box<Self>,
	},
	ExpLet {
		grade: u64,
		grade_argument: u64,
		argument: Box<Self>,
		kind: Box<KindTerm>,
		tail: Binder<Label, Box<Self>>,
	},
	ExpProject(Box<Self>),

	// Dependent functions.
	Pi {
		fragment: Fragment,
		base_kind: Box<KindTerm>,
		base: Box<Self>,
		family_kind: Box<KindTerm>,
		family: Binder<Label, Box<Self>>,
	},
	Function {
		fragment: Fragment,
		domain_kind: Option<Box<KindTerm>>,
		codomain_kind: Option<Box<KindTerm>>,
		body: Binder<Label, Box<Self>>,
	},
	Apply {
		scrutinee: Box<Self>,
		fragment: Option<Fragment>,
		argument: Box<Self>,
		family_kind: Option<Box<KindTerm>>,
	},

	// Dependent pairs.
	Sg {
		base_kind: Box<KindTerm>,
		base: Box<Self>,
		family_kind: Box<KindTerm>,
		family: Binder<Label, Box<Self>>,
	},
	Pair {
		basepoint: Box<Self>,
		fiberpoint: Box<Self>,
	},
	SgLet {
		grade: u64,
		argument: Box<Self>,
		kinds: [Box<KindTerm>; 2],
		tail: Binder<Label, Box<Self>, 2>,
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
		motive: Binder<Label, Box<Self>>,
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
		motive: Binder<Label, Box<Self>, 2>,
		case_refl: Box<Self>,
	},

	// Natural numbers.
	Nat,
	Num(u64),
	Suc(Box<Self>),
	CaseNat {
		scrutinee: Box<Self>,
		motive_kind: Option<Box<KindTerm>>,
		motive: Binder<Label, Box<Self>>,
		case_nil: Box<Self>,
		case_suc: Binder<Label, Box<Self>, 2>,
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
			Repr::Array(n, r) => Self::ReprExp {
				len: *n,
				kind: KindTerm { copy: StaticTerm::CpyNt, repr: Self::from(&**r) }.into(),
			},
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
