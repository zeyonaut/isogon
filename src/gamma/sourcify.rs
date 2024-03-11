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
		Apply { .. }
		| Project { .. }
		| Suc(..)
		| CaseNat { .. }
		| CaseEnum { .. }
		| MaxCopyability(..)
		| ReprPair(..)
		| ReprMax(..)
		| ReprUniv(..) => write_static(term, f, interner),
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
		| Nat
		| Num(..)
		| Enum(..)
		| EnumValue(..)
		| Copyability(..)
		| CopyabilityType
		| ReprType
		| ReprAtom(_) => write_static(term, f, interner),
		Let { .. }
		| Lambda { .. }
		| Pair { .. }
		| Apply { .. }
		| Project { .. }
		| Pi { .. }
		| Sigma { .. }
		| Suc(..)
		| CaseNat { .. }
		| CaseEnum { .. }
		| MaxCopyability(..)
		| ReprPair(_, _)
		| ReprMax(_, _)
		| ReprUniv(_) => {
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
		Pi(base, family) => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
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
		Sigma(base, family) => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				write_static(base, f, interner)?;
				write!(f, "| & ")?;
			} else {
				write_static_spine(base, f, interner)?;
				write!(f, " & ")?;
			}
			write_static(&family.body, f, interner)
		}
		Pair { basepoint, fiberpoint } => {
			write_static_spine(basepoint, f, interner)?;
			write!(f, ", ")?;
			write_static(fiberpoint, f, interner)
		}
		Project(scrutinee, projection) => {
			write_static_spine(scrutinee, f, interner)?;
			match projection {
				Field::Base => write!(f, "/."),
				Field::Fiber => write!(f, "/!"),
			}
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
		Nat => write!(f, "nat"),
		Num(n) => write!(f, "{n}"),
		Suc(prev) => {
			write!(f, "suc ")?;
			write_static_atom(prev, f, interner)
		}
		CaseNat { scrutinee, motive, case_nil, case_suc } => {
			write_static_spine(scrutinee, f, interner)?;
			write!(f, " :: |{}| ", resolve(interner, &motive.parameter()))?;
			write_static(&motive.body, f, interner)?;
			write!(f, " {{0 -> ")?;
			write_static(case_nil, f, interner)?;
			write!(
				f,
				" | suc {} {} -> ",
				resolve(interner, &case_suc.parameters[0]),
				resolve(interner, &case_suc.parameters[1])
			)?;
			write_static(&case_suc.body, f, interner)?;
			write!(f, "}}")
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
		ReprPair(a, b) => {
			write!(f, "rpair ")?;
			write_static_atom(a, f, interner)?;
			write!(f, " ")?;
			write_static_atom(b, f, interner)
		}
		ReprMax(a, b) => {
			write!(f, "rmax ")?;
			write_static_atom(a, f, interner)?;
			write!(f, " ")?;
			write_static_atom(b, f, interner)
		}
		ReprUniv(c) => {
			write!(f, "runiv ")?;
			write_static_atom(c, f, interner)
		}
	}
}

fn write_dynamic_spine(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Apply { .. }
		| Project { .. }
		| Suc(..)
		| CaseNat { .. }
		| CaseEnum { .. }
		| WrapType { .. }
		| WrapNew(_)
		| RcType { .. }
		| RcNew(_)
		| UnRc { .. }
		| Unwrap { .. } => write_dynamic(term, f, interner),
		_ => write_dynamic_atom(term, f, interner),
	}
}

fn write_dynamic_atom(term: &DynamicTerm, f: &mut impl Write, interner: &Rodeo) -> std::fmt::Result {
	use DynamicTerm::*;
	match term {
		Variable(..) | Universe { .. } | Splice(_) | Nat | Num(..) | Enum(..) | EnumValue(..) =>
			write_dynamic(term, f, interner),
		Let { .. }
		| Lambda { .. }
		| Pair { .. }
		| Apply { .. }
		| Project { .. }
		| UnRc { .. }
		| Unwrap { .. }
		| Pi { .. }
		| Sigma { .. }
		| Suc(..)
		| CaseNat { .. }
		| CaseEnum { .. }
		| Id { .. }
		| Refl
		| CasePath { .. }
		| WrapType { .. }
		| WrapNew(_)
		| RcType { .. }
		| RcNew(_) => {
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
		Lambda { body, .. } => {
			write!(f, "|{}| ", resolve(interner, &body.parameter()))?;
			write_dynamic(&body.body, f, interner)
		}
		Apply { scrutinee, argument, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " ")?;
			write_dynamic_atom(argument, f, interner)
		}
		Sigma { base, family, .. } => {
			let parameter = resolve(interner, &family.parameter());
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
			write_dynamic(fiberpoint, f, interner)
		}
		Project { scrutinee, projection, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			match projection {
				Field::Base => write!(f, "/."),
				Field::Fiber => write!(f, "/!"),
			}
		}
		Nat => write!(f, "nat"),
		Num(n) => write!(f, "{n}"),
		Suc(prev) => {
			write!(f, "suc ")?;
			write_dynamic_atom(prev, f, interner)
		}
		CaseNat { scrutinee, motive, case_nil, case_suc, .. } => {
			write_dynamic_spine(scrutinee, f, interner)?;
			write!(f, " :: |{}| ", resolve(interner, &motive.parameter()))?;
			write_dynamic(&motive.body, f, interner)?;
			write!(f, " {{0 -> ")?;
			write_dynamic(case_nil, f, interner)?;
			write!(
				f,
				" | suc @{}.{} -> ",
				resolve(interner, &case_suc.parameters[0]),
				resolve(interner, &case_suc.parameters[1])
			)?;
			write_dynamic(&case_suc.body, f, interner)?;
			write!(f, "}}")
		}
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
		Id { copy, repr, space, left, right } => {
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
		WrapType { inner: x, .. } => {
			write!(f, "Wrap ")?;
			write_dynamic_atom(x, f, interner)
		}
		WrapNew(x) => {
			write!(f, "wrap ")?;
			write_dynamic_atom(x, f, interner)
		}
		Unwrap { scrutinee: x, .. } => {
			write_dynamic_spine(x, f, interner)?;
			write!(f, " unwrap")
		}
		RcType { inner: x, .. } => {
			write!(f, "RC ")?;
			write_dynamic_atom(x, f, interner)
		}
		RcNew(x) => {
			write!(f, "rc ")?;
			write_dynamic_atom(x, f, interner)
		}
		UnRc { scrutinee: x, .. } => {
			write_dynamic_spine(x, f, interner)?;
			write!(f, " unrc")
		}
	}
}
