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
		Apply { .. } | MaxCopyability(..) | CaseEnum { .. } => write_static(term, f, interner),
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
		| ReprAtom(_)
		| Repeat(..)
		| Enum(..)
		| EnumValue(..) => write_static(term, f, interner),
		Let { .. }
		| Lambda { .. }
		| Apply { .. }
		| Pi { .. }
		| MaxCopyability(..)
		| Exp(..)
		| ReprExp(..)
		| LetExp { .. }
		| CaseEnum { .. } => {
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

		Exp(grade, ty) => {
			write!(f, "![{grade}] ")?;
			write_static_atom(ty, f, interner)
		}
		Repeat(grade, tm) => {
			write!(f, "@[{grade}] {{")?;
			write_static(tm, f, interner)?;
			write!(f, "}}")
		}
		LetExp { grade, argument, tail } => {
			write!(f, "let [{grade}] {{{}}} = ", resolve(interner, &tail.parameter()))?;
			write_static(argument, f, interner)?;
			write!(f, "; ")?;
			write_static(&tail.body, f, interner)
		}

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
		Lambda(grade, function) => {
			write!(f, "|[{grade}] {}| ", resolve(interner, &function.parameter()))?;
			write_static(&function.body, f, interner)
		}
		Apply { scrutinee, argument } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_static_atom(argument, f, interner)
		}
		Let { grade, ty, argument, tail } => {
			write!(f, "let [{grade}] {} : ", resolve(interner, &tail.parameter()))?;
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
				// self::ReprAtom::Pointer => "rpointer",
				self::ReprAtom::Byte => "rbyte",
				// self::ReprAtom::Nat => "rnat",
				self::ReprAtom::Fun => "rfun",
			}
		),
		ReprExp(grade, r) => {
			write!(f, "rexp[{grade}] ")?;
			write_static_atom(r, f, interner)
		}
		Enum(k) => write!(f, "#{k}"),
		EnumValue(k, v) => write!(f, "{v}_{k}"),
		CaseEnum { scrutinee, motive, cases } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " :: |{}| ", resolve(interner, &motive.parameter()))?;
			write_static(&motive.body, f, interner)?;
			for (i, case) in cases.iter().enumerate() {
				if i > 0 {
					write!(f, " | ")?;
				}
				write!(f, "{i} -> ")?;
				write_static(case, f, interner)?;
			}
			write!(f, "}}")
		}
	}
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. } | CaseEnum { .. } => write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe { .. } | Splice(_) | Repeat(..) | Enum(..) | EnumValue(..) | Refl =>
			write_dynamic(term, f, interner),
		Let { .. }
		| Function { .. }
		| Apply { .. }
		| Pi { .. }
		| LetExp { .. }
		| Exp(..)
		| CaseEnum { .. }
		| Id { .. }
		| CasePath { .. } => {
			write!(f, "(")?;
			write_dynamic(term, f, interner)?;
			write!(f, ")")
		}
	}
}

pub fn write_dynamic(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		// Variables.
		Variable(name, ..) => write!(f, "{}", resolve(interner, name)),

		// Let-expressions.
		Let { grade, ty, argument, tail } => {
			write!(f, "let [{grade}] {} : ", resolve(interner, &tail.parameter()))?;
			write_dynamic(ty, f, interner)?;
			write!(f, " = ")?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(&tail.body, f, interner)
		}

		// Types.
		Universe { copyability, representation } => {
			write!(f, "* ")?;
			write_static_atom(&copyability, f, interner)?;
			write!(f, " ")?;
			write_static_atom(&representation, f, interner)
		}

		// Quoted programs.
		Splice(splicee) => {
			write!(f, "[")?;
			write_static(splicee, f, interner)?;
			write!(f, "]")
		}

		// Repeated programs.
		Exp(grade, ty) => {
			write!(f, "![{grade}] ")?;
			write_dynamic_atom(ty, f, interner)
		}
		Repeat(grade, tm) => {
			write!(f, "@[{grade}] {{")?;
			write_dynamic(tm, f, interner)?;
			write!(f, "}}")
		}
		LetExp { grade, argument, tail } => {
			write!(f, "let [{grade}] {{{}}} = ", resolve(interner, &tail.parameter()))?;
			write_dynamic(argument, f, interner)?;
			write!(f, "; ")?;
			write_dynamic(&tail.body, f, interner)
		}

		// Dependent functions.
		Pi { grade, base, family, .. } => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|[{grade}] {parameter} : ")?;
				write_dynamic(base, f, interner)?;
				write!(f, "| -> ")?;
			} else {
				write_dynamic_spine(base, f, interner)?;
				write!(f, " [{grade}] -> ")?;
			}
			write_dynamic(&family.body, f, interner)
		}
		Function { grade, body, .. } => {
			write!(f, "|[{grade}] {}| ", resolve(interner, &body.parameter()))?;
			write_dynamic(&body.body, f, interner)
		}
		Apply { scrutinee, argument, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}

		// Enumerated numbers.
		Enum(k) => write!(f, "#{k}"),
		EnumValue(k, v) => write!(f, "{v}_{k}"),
		CaseEnum { scrutinee, motive, cases, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " :: bool |{}| ", resolve(interner, &motive.parameter()))?;
			write_dynamic(&motive.body, f, interner)?;
			write!(f, " {{")?;
			for (i, case) in cases.iter().enumerate() {
				if i > 0 {
					write!(f, " | ")?;
				}
				write!(f, "{i} -> ")?;
				write_dynamic(case, f, interner)?;
			}
			write!(f, "}}")
		}
		// Paths.
		Id { copy: _, repr: _, space, left, right } => {
			write!(f, "Id ")?;
			write_dynamic_atom(space, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(left, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(right, f, interner)
		}
		Refl => write!(f, "refl"),
		CasePath { scrutinee, motive, case_refl } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(
				f,
				" :: |{}.{}| ",
				resolve(interner, &motive.parameters[0]),
				resolve(interner, &motive.parameters[1]),
			)?;
			write_dynamic(&motive.body, f, interner)?;
			write!(f, " {{refl -> ")?;
			write_dynamic(case_refl, f, interner)?;
			write!(f, "}}")
		}
	}
}
