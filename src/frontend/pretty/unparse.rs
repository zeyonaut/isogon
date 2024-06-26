use std::fmt::Write;

use lasso::Resolver;

use crate::{
	common::{Cost, Cpy, Field, Fragment, Label, Name, ReprAtom},
	ir::presyntax::{Constructor, Former, IrrefutablePattern, Pattern, Preterm, Projector, PurePreterm},
};

pub fn pretty_print(term: &PurePreterm, interner: &impl Resolver) -> String {
	let mut s = String::new();
	print(term, &mut s, interner).unwrap();
	s
}

pub fn print(preterm: &PurePreterm, f: &mut impl Write, interner: &impl Resolver) -> std::fmt::Result {
	match &preterm.0 {
		Preterm::Variable(name) => write!(f, "{}", interner.resolve(name))?,
		Preterm::Index(index) => write!(f, "_{}", index.0)?,
		Preterm::Let { is_meta, grade, tys, argument, pattern, tail } => {
			write!(f, "{} ", if *is_meta { "def" } else { "let" })?;
			if let Some(grade) = grade {
				write!(f, "[{}] ", cost(*grade))?;
			}
			print_irrefutable_pattern(pattern, f, interner)?;
			for ty in tys {
				write!(f, " : ")?;
				print(ty, f, interner)?;
			}
			write!(f, " = ")?;
			print(argument, f, interner)?;
			write!(f, "; ")?;
			print(tail, f, interner)?;
		}
		Preterm::SwitchLevel(t) => {
			write!(f, "<")?;
			print(t, f, interner)?;
			write!(f, ">")?;
		}
		Preterm::Pi { fragment, base, family } => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				print(base, f, interner)?;
				write!(f, "|")?;
			} else {
				print_spine(base, f, interner)?;
			}
			match fragment {
				Fragment::Logical => write!(f, " @ -> ")?,
				Fragment::Material => write!(f, " -> ")?,
			}
			print(&family.body, f, interner)?
		}
		Preterm::Lambda { body } => {
			let parameter = resolve(interner, &body.parameter());
			write!(f, "|{parameter}| ")?;
			print(&body.body, f, interner)?;
		}
		Preterm::Call { callee, argument } => {
			print_spine(callee, f, interner)?;
			write!(f, " ")?;
			print_atom(argument, f, interner)?;
		}
		Preterm::Sg { base, family } => {
			let parameter = resolve(interner, &family.parameter());
			if parameter != "_" {
				write!(f, "|{parameter} : ")?;
				print(base, f, interner)?;
				write!(f, "| & ")?;
			} else {
				print_spine(base, f, interner)?;
				write!(f, " & ")?;
			}
			print(&family.body, f, interner)?;
		}
		Preterm::Pair { basepoint, fiberpoint } => {
			print_spine(basepoint, f, interner)?;
			write!(f, ", ")?;
			print(fiberpoint, f, interner)?;
		}
		Preterm::Former(former, args) => {
			print_former(former, f, interner)?;
			for arg in args {
				write!(f, " ")?;
				print_atom(arg, f, interner)?;
			}
		}
		Preterm::Constructor(constructor, args) => {
			print_constructor(constructor, f, interner)?;
			for arg in args {
				write!(f, " ")?;
				print_atom(arg, f, interner)?;
			}
		}
		Preterm::Project(head, projector) => {
			print_spine(head, f, interner)?;
			write!(f, " ")?;
			print_projector(projector, f, interner)?;
		}
		Preterm::Split { scrutinee, is_cast, motive, cases } => {
			print_spine(scrutinee, f, interner)?;
			if *is_cast {
				write!(f, " cast")?;
			}
			write!(f, " :: |")?;
			print_multiparameter(&motive.parameters, f, interner)?;
			write!(f, "| ")?;
			print_spine(&motive.body, f, interner)?;
			write!(f, " {{")?;

			let mut cases = cases.iter();
			if let Some((pattern, preterm)) = cases.next() {
				print_pattern(pattern, f, interner)?;
				write!(f, " -> ")?;
				print(preterm, f, interner)?;
				for (pattern, preterm) in cases {
					write!(f, " | ")?;
					print_pattern(pattern, f, interner)?;
					write!(f, " -> ")?;
					print(preterm, f, interner)?;
				}
			}

			write!(f, "}}")?;
		}
	}

	Ok(())
}

fn print_irrefutable_pattern(
	pattern: &IrrefutablePattern<Label>,
	f: &mut impl Write,
	interner: &impl Resolver,
) -> std::fmt::Result {
	match pattern {
		IrrefutablePattern::Label(label) => write!(f, "{}", resolve(interner, label)),
		IrrefutablePattern::Exp(grade, label) =>
			write!(f, "@[{}] {} = ", cost(*grade), resolve(interner, label)),
		IrrefutablePattern::Pair([a, b]) => write!(f, "({}, {})", resolve(interner, a), resolve(interner, b)),
	}
}

fn print_spine(preterm: &PurePreterm, f: &mut impl Write, interner: &impl Resolver) -> std::fmt::Result {
	match &preterm.0 {
		Preterm::Call { .. }
		| Preterm::Former(..)
		| Preterm::Constructor(..)
		| Preterm::Project(..)
		| Preterm::Split { .. } => print(preterm, f, interner),
		_ => print_atom(preterm, f, interner),
	}
}

fn print_atom(preterm: &PurePreterm, f: &mut impl Write, interner: &impl Resolver) -> std::fmt::Result {
	match &preterm.0 {
		Preterm::Variable(_) | Preterm::Index(_) | Preterm::SwitchLevel(_) => print(preterm, f, interner)?,

		Preterm::Constructor(_, args) | Preterm::Former(_, args) if args.is_empty() =>
			print(preterm, f, interner)?,

		Preterm::Let { .. }
		| Preterm::Pi { .. }
		| Preterm::Lambda { .. }
		| Preterm::Call { .. }
		| Preterm::Sg { .. }
		| Preterm::Pair { .. }
		| Preterm::Former(..)
		| Preterm::Constructor(..)
		| Preterm::Project(..)
		| Preterm::Split { .. } => {
			write!(f, "(")?;
			print(preterm, f, interner)?;
			write!(f, ")")?;
		}
	}
	Ok(())
}

fn print_former(former: &Former, f: &mut impl Write, _: &impl Resolver) -> std::fmt::Result {
	match former {
		Former::Universe => write!(f, "*"),
		Former::Copy => write!(f, "copy"),
		Former::Repr => write!(f, "repr"),
		Former::Lift => write!(f, "'"),
		Former::Exp(grade) => write!(f, "![{}] ", cost(*grade)),
		Former::Enum(2) => write!(f, "Bool"),
		Former::Enum(k) => write!(f, "#{k}"),
		Former::Id => write!(f, "Id"),
		Former::Nat => write!(f, "Nat"),
		Former::Bx => write!(f, "Box"),
		Former::Wrap => write!(f, "Wrap"),
	}
}

fn print_constructor(constructor: &Constructor, f: &mut impl Write, _: &impl Resolver) -> std::fmt::Result {
	match constructor {
		Constructor::Cpy(Cpy::Tr) => write!(f, "c0"),
		Constructor::Cpy(Cpy::Nt) => write!(f, "c1"),
		Constructor::CpyMax => write!(f, "cmax"),
		Constructor::ReprAtom(None) => write!(f, "rnone"),
		Constructor::ReprAtom(Some(r)) => write!(
			f,
			"{}",
			match r {
				self::ReprAtom::Byte => "rbyte",
				self::ReprAtom::Nat => "rnat",
				self::ReprAtom::Ptr => "rptr",
				self::ReprAtom::Fun => "rfun",
			}
		),
		Constructor::ReprExp(grade) => write!(f, "rexp[{grade}]"),
		Constructor::ReprPair => write!(f, "rpair"),
		Constructor::ReprMax => write!(f, "rmax"),
		Constructor::Exp(grade) => write!(f, "@[{}]", cost(*grade)),
		Constructor::Enum(2, 0) => write!(f, "false"),
		Constructor::Enum(2, 1) => write!(f, "true"),
		Constructor::Enum(k, v) => write!(f, "{v}_{k}"),
		Constructor::Refl => write!(f, "refl"),
		Constructor::Num(n) => write!(f, "{n}"),
		Constructor::Suc => write!(f, "suc"),
		Constructor::Bx => write!(f, "box"),
		Constructor::Wrap => write!(f, "wrap"),
	}
}

fn print_projector(projector: &Projector, f: &mut impl Write, _: &impl Resolver) -> std::fmt::Result {
	match projector {
		Projector::Exp => write!(f, "unexp"),
		Projector::Bx => write!(f, "unbox"),
		Projector::Wrap => write!(f, "unwrap"),
		Projector::Field(Field::Base) => write!(f, "/."),
		Projector::Field(Field::Fiber) => write!(f, "/!"),
	}
}

fn print_pattern(pattern: &Pattern<Label>, f: &mut impl Write, interner: &impl Resolver) -> std::fmt::Result {
	match pattern {
		Pattern::Variable(name) => write!(f, "{}", resolve(interner, name))?,
		Pattern::Witness { index, witness } => {
			write!(f, "@")?;
			write!(f, "{}", resolve(interner, index))?;
			write!(f, ".")?;
			write!(f, "{}", resolve(interner, witness))?;
		}
		// NOTE: Does not currently work with constructors applied to constructors.
		Pattern::Construction(constructor, patterns) => {
			print_constructor(constructor, f, interner)?;
			for pattern in patterns {
				write!(f, " ")?;
				print_pattern(pattern, f, interner)?;
			}
		}
	}
	Ok(())
}

fn print_multiparameter(
	parameters: &[Option<Name>],
	f: &mut impl Write,
	interner: &impl Resolver,
) -> std::fmt::Result {
	let mut parameters = parameters.iter();
	if let Some(first) = parameters.next() {
		write!(f, "{}", resolve(interner, first))?;
		for parameter in parameters {
			write!(f, ".{}", resolve(interner, parameter))?;
		}
	}
	Ok(())
}

fn resolve<'a>(interner: &'a impl Resolver, name: &Option<Name>) -> &'a str {
	if let Some(name) = name {
		interner.resolve(name)
	} else {
		"_"
	}
}

fn cost(grade: Cost) -> String {
	if let Cost::Fin(grade) = grade {
		format!("{grade}")
	} else {
		"*".to_owned()
	}
}
