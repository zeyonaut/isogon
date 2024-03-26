use std::fmt::Write;

use lasso::Rodeo;

use super::{
	common::{Copyability, Field, Name, ReprAtom},
	ir::syntax::{DynamicTerm, StaticTerm},
};

fn write_static_spine(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		// Any case which is not already covered by write_static_atom.
		Apply { .. } | MaxCopyability(..) | ReprUniv(..) => write_static(term, f, interner),
		_ => write_static_atom(term, f, interner),
	}
}

fn write_static_atom(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;
	match term {
		Variable(..)
		| Universe
		| Lift { .. }
		| Quote(_)
		| Copyability(..)
		| CopyabilityType
		| ReprType
		| ReprAtom(_) => write_static(term, f, interner),
		Let { .. } | Lambda { .. } | Apply { .. } | Pi { .. } | MaxCopyability(..) | ReprUniv(_) => {
			write!(f, "(")?;
			write_static(term, f, interner)?;
			write!(f, ")")
		}
	}
}

fn resolve<'a>(interner: &'a Rodeo, name: &Option<Name>) -> &'a str {
	if let Some(name) = name {
		interner.resolve(name)
	} else {
		"_"
	}
}

fn write_static(term: &StaticTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use StaticTerm::*;

	use self::Copyability as C;
	match term {
		Variable(name, ..) => write!(f, "{}", resolve(interner, name)),
		CopyabilityType => write!(f, "copy"),
		Copyability(C::Trivial) => write!(f, "c0"),
		Copyability(C::Nontrivial) => write!(f, "c1"),
		MaxCopyability(a, b) => {
			write!(f, "cmax ")?;
			write_static_atom(a, f, interner)?;
			write!(f, " ")?;
			write_static_atom(b, f, interner)
		}
		Pi(grade, base, family) => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} @ {grade:?} : ")?;
				write_static(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_static_spine(base, f, interner)?;
				write!(f, " -> ")?;
			}
			write_static(&family.body, f, interner)
		}
		Lambda(function) => {
			write!(f, "|{}| ", resolve(interner, &function.parameter()))?;
			write_static(&function.body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_static_atom(argument, f, interner)
		}
		Let { ty, argument, tail } => {
			write!(f, "let {} : ", resolve(interner, &tail.parameter()))?;
			write_static(ty, f, interner)?;
			write!(f, " = ")?;
			write_static(argument, f, interner)?;
			write!(f, "; ")?;
			write_static(&tail.body, f, interner)
		}
		Universe => write!(f, "*"),
		Lift { liftee, .. } => {
			write!(f, "'")?;
			write_dynamic_atom(liftee, f, interner)
		}
		Quote(quotee) => {
			write!(f, "<")?;
			write_dynamic(quotee, f, interner)?;
			write!(f, ">")
		}
		ReprType => write!(f, "repr"),
		ReprAtom(None) => write!(f, "rnone"),
		ReprAtom(Some(r)) => write!(
			f,
			"{}",
			match r {
				self::ReprAtom::Class => "rclass",
				self::ReprAtom::Pointer => "rpointer",
				self::ReprAtom::Byte => "rbyte",
				self::ReprAtom::Nat => "rnat",
				self::ReprAtom::Fun => "rfun",
			}
		),
		ReprUniv(c) => {
			write!(f, "runiv ")?;
			write_static_atom(c, f, interner)
		}
	}
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } => write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe { .. } | Splice(_) => write_dynamic(term, f, interner),
		Let { .. } | Function { .. } | Apply { .. } | Pi { .. } => {
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
			write!(f, "let {} : ", resolve(interner, &tail.parameter()))?;
			write_dynamic(ty, f, interner)?;
			write!(f, " = ")?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(&tail.body, f, interner)
		}
		Variable(name, ..) => write!(f, "{}", resolve(interner, name)),
		Splice(splicee) => {
			write!(f, "[")?;
			write_static(splicee, f, interner)?;
			write!(f, "]")
		}
		Universe { copyability, representation } => {
			write!(f, "* ")?;
			write_static_atom(&copyability, f, interner)?;
			write!(f, " ")?;
			write_static_atom(&representation, f, interner)
		}
		Pi { base, family, .. } => {
			let parameter = resolve(interner, &family.parameter());
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
		Function { body, .. } => {
			write!(f, "|{}| ", resolve(interner, &body.parameter()))?;
			write_dynamic(&body.body, f, interner)
		}
		Apply { scrutinee, argument, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}
	}
}
