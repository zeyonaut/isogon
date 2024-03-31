use crate::delta::common::{Binder, Cpy, Field, Index, Name, Repr, ReprAtom};

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

	ReprType,
	ReprAtom(Option<ReprAtom>),
	ReprExp(usize, Box<Self>),

	// Quoted programs.
	Lift { liftee: Box<DynamicTerm>, copy: Box<Self>, repr: Box<Self> },
	Quote(Box<DynamicTerm>),

	// Repeated programs.
	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp { grade: usize, argument: Box<Self>, tail: Binder<Box<Self>> },

	// Dependent functions.
	Pi(usize, Box<Self>, Binder<Box<Self>>),
	Lambda(usize, Binder<Box<Self>>),
	Apply { scrutinee: Box<Self>, argument: Box<Self> },

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum { scrutinee: Box<Self>, motive: Binder<Box<Self>>, cases: Vec<Self> },
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
		copyability: Box<StaticTerm>,
		representation: Box<StaticTerm>,
	},

	// Quoted programs.
	Splice(Box<StaticTerm>),

	// Repeated programs.
	Exp(usize, Box<Self>),
	Repeat(usize, Box<Self>),
	LetExp {
		grade: usize,
		argument: Box<Self>,
		tail: Binder<Box<Self>>,
	},

	// Dependent functions.
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

	// Enumerated numbers.
	Enum(u16),
	EnumValue(u16, u8),
	CaseEnum {
		scrutinee: Box<Self>,
		cases: Vec<Self>,
		fiber_copyability: Box<StaticTerm>,
		fiber_representation: Box<StaticTerm>,
		motive: Binder<Box<Self>>,
	},

	// Paths.
	Id {
		copy: Box<StaticTerm>,
		repr: Box<StaticTerm>,
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
		inner: Box<Self>,
		copy: Box<StaticTerm>,
		repr: Box<StaticTerm>,
	},
	BxValue(Box<Self>),
	BxProject {
		scrutinee: Box<Self>,
		copy: Box<StaticTerm>,
		repr: Box<StaticTerm>,
	},
	Wrap {
		inner: Box<Self>,
		copy: Box<StaticTerm>,
		repr: Box<StaticTerm>,
	},
	WrapValue(Box<Self>),
	WrapProject {
		scrutinee: Box<Self>,
		copy: Box<StaticTerm>,
		repr: Box<StaticTerm>,
	},
}
