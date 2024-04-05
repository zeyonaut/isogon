use std::collections::HashMap;

use super::stage::Stage;
use crate::delta::{
	common::{Binder, Cost, Index, Level, Repr, ReprAtom},
	ir::{
		flat::{Capture, Function, Parameter, Procedure, Program, Substitute, Term, Variable},
		syntax::DynamicTerm,
	},
};

/// Performs closure-conversion on an object term, hoisting all functions to top level.
pub fn flatten(value: &DynamicTerm) -> Program {
	let mut flattener = Flattener { amplifiers: vec![], context: vec![], procedures: vec![] };

	let entry = flattener.flatten(&value, &mut vec![]);

	Program { entry, procedures: flattener.procedures }
}

struct Flattener {
	amplifiers: Vec<(usize, Cost)>,
	context: Vec<Parameter>,
	procedures: Vec<Procedure>,
}

impl Flattener {
	// Gives the number of copies of the given variable are used given a reference to one.
	fn usage(&self, level: usize) -> Cost {
		self
			.amplifiers
			.iter()
			.rev()
			.take_while(|(len, _)| level < *len)
			.fold(Cost::Fin(1), |agg, (_, amp)| agg * *amp)
	}

	fn flatten(&mut self, value: &DynamicTerm, occurrences: &mut Vec<Cost>) -> Term {
		match value {
			// Variables.
			DynamicTerm::Variable(name, Index(i)) => {
				let l = self.context.len() - (i + 1);
				if let Some(l_occurrences) = occurrences.get_mut(l) {
					*l_occurrences += if self.context[l].grade == Cost::Inf { Cost::Inf } else { self.usage(l) }
				}
				Term::Variable(*name, Variable::Local(Level(l)))
			}

			// Let-expressions.
			DynamicTerm::Def { .. } => panic!("unstaged"),
			DynamicTerm::Let { grade, ty: _, argument_kind, argument, tail } => {
				let repr = argument_kind.clone().stage().repr;
				Term::Let {
					grade: *grade,
					argument_repr: repr.clone(),
					argument: if *grade == 0 {
						Term::Irrelevant
					} else {
						self.amplifiers.push((self.context.len(), Cost::Fin(*grade)));
						let argument = self.flatten(argument, occurrences);
						self.amplifiers.pop();
						argument
					}
					.into(),
					tail: self.flatten_with(tail, [Cost::Fin(*grade)], [repr], occurrences),
				}
			}

			// Types.
			DynamicTerm::Universe { .. } => panic!("irrelevant"),

			// Quoted programs.
			DynamicTerm::Splice(..) => panic!("unstaged"),

			// Repeated programs.
			DynamicTerm::Exp(..) => panic!("irrelevant"),
			DynamicTerm::Repeat(_, _) => unimplemented!(),
			DynamicTerm::LetExp { grade, grade_argument, argument, tail } => unimplemented!(),

			// Dependent functions.
			DynamicTerm::Pi { .. } => panic!("irrelevant"),
			DynamicTerm::Function { grade, domain_kind, codomain_kind, body } =>
				Term::Function(self.flatten_function(
					Cost::Fin(*grade),
					domain_kind.clone().unwrap().stage().repr,
					body,
					codomain_kind.clone().unwrap().stage().repr,
					occurrences,
				)),
			DynamicTerm::Apply { scrutinee, grade, argument, family_kind } => Term::Apply {
				callee: self.flatten(scrutinee, occurrences).into(),
				argument: {
					let grade = grade.unwrap();
					if grade == 0 {
						Term::Irrelevant
					} else {
						self.amplifiers.push((self.context.len(), Cost::Fin(grade)));
						let argument = self.flatten(argument, occurrences);
						self.amplifiers.pop();
						argument
					}
				}
				.into(),
				result_repr: family_kind.clone().unwrap().stage().repr,
			},

			// Dependent pairs.
			DynamicTerm::Sg { .. } => panic!("irrelevant"),
			DynamicTerm::Pair { basepoint, fiberpoint } => Term::Pair {
				basepoint: self.flatten(basepoint, occurrences).into(),
				fiberpoint: self.flatten(fiberpoint, occurrences).into(),
			},
			DynamicTerm::SgLet { grade, argument, kinds, tail } => {
				let reprs = kinds.each_ref().map(|kind| kind.clone().stage().repr);
				Term::SgLet {
					grade: *grade,
					argument: if *grade == 0 {
						Term::Irrelevant
					} else {
						self.amplifiers.push((self.context.len(), Cost::Fin(*grade)));
						let argument = self.flatten(argument, occurrences);
						self.amplifiers.pop();
						argument
					}
					.into(),
					bound_reprs: reprs.clone(),
					tail: self.flatten_with(tail, [Cost::Fin(*grade); 2], reprs, occurrences),
				}
			}
			DynamicTerm::SgField { .. } => panic!("irrelevant"),

			// Enumerated numbers.
			DynamicTerm::Enum(..) => panic!("irrelevant"),
			DynamicTerm::EnumValue(k, v) => Term::EnumValue(*k, *v),
			DynamicTerm::CaseEnum { scrutinee, motive_kind, motive: _, cases } => Term::CaseEnum {
				scrutinee: self.flatten(scrutinee, occurrences).into(),
				cases: cases.into_iter().map(|case| self.flatten(case, occurrences)).collect(),
				motive_repr: motive_kind.clone().unwrap().stage().repr,
			},

			// Paths.
			DynamicTerm::Id { .. } | DynamicTerm::Refl => panic!("irrelevant"),
			DynamicTerm::CasePath { case_refl, .. } => self.flatten(&case_refl, occurrences),

			// Natural numbers.
			DynamicTerm::Nat => panic!("irrelevant"),
			DynamicTerm::Num(n) => Term::Num(*n),
			DynamicTerm::Suc(tm) => Term::Suc(self.flatten(tm, occurrences).into()),
			DynamicTerm::CaseNat { scrutinee, motive_kind, motive: _, case_nil, case_suc } => Term::CaseNat {
				scrutinee: self.flatten(scrutinee, occurrences).into(),
				case_nil: self.flatten(case_nil, occurrences).into(),
				case_suc: {
					self.amplifiers.push((self.context.len(), Cost::Inf));
					// NOTE: This uses the fact that naturals are trivial.
					let result = self.flatten_with(
						case_suc,
						[Cost::Inf, 1.into()],
						[Some(Repr::Atom(ReprAtom::Nat)), motive_kind.clone().unwrap().stage().repr],
						occurrences,
					);
					self.amplifiers.pop();
					result
				},
				motive_repr: motive_kind.clone().unwrap().stage().repr,
			},

			// Wrappers.
			DynamicTerm::Bx { .. } => panic!("irrelevant"),
			DynamicTerm::BxValue(tm) => Term::BxValue(self.flatten(tm, occurrences).into()),
			DynamicTerm::BxProject { kind, scrutinee } =>
				Term::BxProject(self.flatten(scrutinee, occurrences).into(), kind.clone().unwrap().stage().repr),

			DynamicTerm::Wrap { .. } => panic!("irrelevant"),
			DynamicTerm::WrapValue(tm) => Term::WrapValue(self.flatten(tm, occurrences).into()),
			DynamicTerm::WrapProject { kind, scrutinee } =>
				Term::WrapProject(self.flatten(scrutinee, occurrences).into(), kind.clone().unwrap().stage().repr),
		}
	}

	fn flatten_function(
		&mut self,
		grade: Cost,
		repr: Option<Repr>,
		body: &Binder<Box<DynamicTerm>>,
		result_repr: Option<Repr>,
		occurrences: &mut Vec<Cost>,
	) -> Function {
		let context_len = Level(self.context.len());

		// Find free occurrents in the function body.
		let mut body_occurrences = vec![Cost::Fin(0); context_len.0];
		let mut body = self.flatten_with(body, [grade], [repr.clone()], &mut body_occurrences);

		// Update the external free occurrence set.
		for (outer, inner) in occurrences.iter_mut().zip(&mut body_occurrences) {
			*outer += *inner;
		}

		// Construct a partial substitution mapping occurrent levels to capture levels.
		let (captures, captured_parameters, sub) = {
			let mut captures = Vec::new();
			let mut captured_parameters = Vec::new();
			let mut sub = HashMap::new();
			let mut count = 0;
			for (l, l_occurrences) in body_occurrences.iter().enumerate() {
				if l_occurrences != &Cost::Fin(0) {
					let parameter = &self.context[l];
					captures.push(Capture {
						name: parameter.name,
						variable: Variable::Local(Level(l)),
						cost: *l_occurrences,
					});
					captured_parameters.push(Parameter {
						name: parameter.name,
						grade: *l_occurrences,
						repr: parameter.repr.clone(),
					});
					sub.insert(Level(l), Level(count));
					count += 1;
				}
			}
			(captures, captured_parameters, sub)
		};

		// Perform the substitution on the body.
		body.substitute(&sub, context_len);
		let Binder { parameters: [parameter_name], body } = body;

		let procedure = Procedure {
			captured_parameters,
			parameter: Parameter { name: parameter_name, grade, repr },
			body: *body,
			result_repr,
		};

		let procedure_id = self.procedures.len();
		self.procedures.push(procedure);

		Function { procedure_id, captures }
	}

	fn flatten_with<const N: usize>(
		&mut self,
		binder: &Binder<Box<DynamicTerm>, N>,
		grades: [Cost; N],
		reprs: [Option<Repr>; N],
		occurrences: &mut Vec<Cost>,
	) -> Binder<Box<Term>, N> {
		let level = self.context.len();
		self.context.extend(
			binder
				.parameters
				.into_iter()
				.zip(grades.into_iter().zip(reprs))
				.map(|(name, (grade, repr))| Parameter { name, grade, repr }),
		);
		let result = binder.map_ref(|body| self.flatten(body, occurrences));
		self.context.truncate(level);
		result
	}
}