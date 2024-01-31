use crate::gamma::common::{Binder, Copyability, Name, Projection, ReprAtom};

#[derive(Debug, Clone)]
pub enum StaticPreterm {
	Variable(Name),
	Let {
		assignee: Name,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Box<Self>,
	},
	Lift(Box<DynamicPreterm>),
	Quote(Box<DynamicPreterm>),
	Universe,
	Pi {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Lambda {
		parameter: Name,
		body: Box<Self>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
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
		motive_parameter: Name,
		motive: Box<Self>,
		case_nil: Box<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Box<Self>,
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

#[derive(Debug, Clone)]
pub enum DynamicPreterm {
	Variable(Name),
	Let {
		assignee: Name,
		ty: Box<Self>,
		argument: Box<Self>,
		tail: Box<Self>,
	},
	Splice(Box<StaticPreterm>),
	WrapType(Box<Self>),
	WrapNew(Box<Self>),
	Unwrap(Box<Self>),
	RcType(Box<Self>),
	RcNew(Box<Self>),
	UnRc(Box<Self>),
	Universe {
		copyability: Box<StaticPreterm>,
		representation: Box<StaticPreterm>,
	},
	Pi {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
	},
	Lambda {
		parameter: Name,
		body: Box<Self>,
	},
	Apply {
		scrutinee: Box<Self>,
		argument: Box<Self>,
	},
	Sigma {
		parameter: Name,
		base: Box<Self>,
		family: Box<Self>,
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
		motive_parameter: Name,
		motive: Box<Self>,
		case_nil: Box<Self>,
		case_suc_parameters: (Name, Name),
		case_suc: Box<Self>,
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
