use std::fmt::Write;

use lasso::Rodeo;

use super::{
	common::Projection,
	elaborator::{DynamicTerm, StaticTerm},
};

fn write_static_spine(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Apply { .. } => write_static(term, f, interner),
		_ => write_static_atom(term, f, interner),
	}
}

fn write_static_atom(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(..) | Universe | Lift(_) | Quote(_) => write_static(term, f, interner),
		Lambda { .. } | Apply { .. } | Pi { .. } | Let { .. } => {
			write!(f, "(")?;
			write_static(term, f, interner)?;
			write!(f, ")")
		}
	}
}

fn write_static(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(name, ..) => write!(f, "{}", interner.resolve(name)),
		Lambda(function) => {
			write!(f, "|{}| ", interner.resolve(&function.parameter()))?;
			write_static(&function.body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_static_atom(argument, f, interner)
		}
		Pi(base, family) => {
			let parameter = interner.resolve(&family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_static(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_static(base, f, interner)?;
				write!(f, " -> ")?;
			}
			write_static(&family.body, f, interner)
		}
		Let { ty, argument, tail } => {
			write!(f, "let {} : ", interner.resolve(&tail.parameter()))?;
			write_static(ty, f, interner)?;
			write!(f, " = ")?;
			write_static(argument, f, interner)?;
			write!(f, "; ")?;
			write_static(&tail.body, f, interner)
		}
		Universe => write!(f, "*"),
		Lift(liftee) => {
			write!(f, "'")?;
			write_dynamic_atom(liftee, f, interner)
		}
		Quote(quotee) => {
			write!(f, "[")?;
			write_dynamic(quotee, f, interner)?;
			write!(f, "]")
		}
	}
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } | Project { .. } | Suc(..) | CaseNat { .. } | CaseBool { .. } =>
			write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe | Splice(_) | Nat | Num(..) | Bool | BoolValue(..) =>
			write_dynamic(term, f, interner),
		Let { .. }
		| Lambda { .. }
		| Pair { .. }
		| Apply { .. }
		| Project { .. }
		| Pi { .. }
		| Sigma { .. }
		| Suc(..)
		| CaseNat { .. }
		| CaseBool { .. } => {
			write!(f, "(")?;
			write_dynamic(term, f, interner)?;
			write!(f, ")")
		}
	}
}

pub fn write_dynamic(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Let { ty, argument, tail } => {
			write!(f, "let {} : ", interner.resolve(&tail.parameter()))?;
			write_dynamic(ty, f, interner)?;
			write!(f, " = ")?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(&tail.body, f, interner)
		}
		Variable(name, ..) => write!(f, "{}", interner.resolve(name)),
		Splice(splicee) => {
			write!(f, "[")?;
			write_static(splicee, f, interner)?;
			write!(f, "]")
		}
		Universe => write!(f, "*"),
		Pi(base, family) => {
			let parameter = interner.resolve(&family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_dynamic(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_dynamic_spine(base, f, interner)?;
				write!(f, " -> ")?;
			}
			write_dynamic(&family.body, f, interner)
		}
		Lambda(function) => {
			write!(f, "|{}| ", interner.resolve(&function.parameter()))?;
			write_dynamic(&function.body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}
		Sigma(base, family) => {
			let parameter = interner.resolve(&family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_dynamic(base, f, interner)?;
				write!(f, "| & ")?;
			} else {
				write_dynamic_spine(base, f, interner)?;
				write!(f, " & ")?;
			}
			write_dynamic(&family.body, f, interner)
		}
		Pair { basepoint, fiberpoint } => {
			write_dynamic_spine(basepoint, f, interner)?;
			write!(f, ", ")?;
			write_dynamic_spine(fiberpoint, f, interner)
		}
		Project(scrutinee, projection) => {
			write_dynamic_spine(scrutinee, f, interner)?;
			match projection {
				Projection::Base => write!(f, "/."),
				Projection::Fiber => write!(f, "/!"),
			}
		}
		Nat => write!(f, "nat"),
		Num(n) => write!(f, "{n}"),
		Suc(prev) => {
			write!(f, "suc ")?;
			write_dynamic_atom(prev, f, interner)
		}
		CaseNat { scrutinee, motive, case_nil, case_suc } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " :: |{}| ", interner.resolve(&motive.parameter()))?;
			write_dynamic(&motive.body, f, interner)?;
			write!(f, " {{0 -> ")?;
			write_dynamic(case_nil, f, interner)?;
			write!(
				f,
				" | suc {} {} -> ",
				interner.resolve(&case_suc.parameters[0]),
				interner.resolve(&case_suc.parameters[1])
			)?;
			write_dynamic(&case_suc.body, f, interner)?;
			write!(f, "}}")
		}
		Bool => write!(f, "bool"),
		BoolValue(b) => write!(f, "{}", if *b { "true" } else { "false" }),
		CaseBool { scrutinee, motive, case_false, case_true } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " :: bool |{}| ", interner.resolve(&motive.parameter()))?;
			write_dynamic(&motive.body, f, interner)?;
			write!(f, " {{false -> ")?;
			write_dynamic(case_false, f, interner)?;
			write!(f, " | true -> ")?;
			write_dynamic(case_true, f, interner)?;
			write!(f, "}}")
		}
	}
}
