package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;

public class EqualityExtractor {
	public static class Equations {
		/**
		 * The outer set stores the different possible sets of equations that form a valid way of updating. It is a
		 * disjunction of conjunctions.
		 */
		protected final Set<Set<Equation>> mEquations;

		protected Equations(final Equation equation) {
			final HashSet<Equation> andConjunct = new HashSet<>();
			andConjunct.add(equation);
			mEquations = new HashSet<>();
			mEquations.add(andConjunct);
		}

		public Equations(final Set<Set<Equation>> equations) {
			mEquations = equations;
		}

		public Equations() {
			this(new HashSet<>());
		}

		public void and(final Equations equationsB, final ManagedScript script) {
			if (mEquations.isEmpty()) {
				mEquations.add(new HashSet<>());
			}

			final Set<Set<Equation>> newElements = new HashSet<>();

			// Distributivity, make a conjunct from each pair of conjuncts.
			for (final Set<Equation> equationSet : mEquations) {
				for (final Set<Equation> equationSetB : equationsB.mEquations) {
					final HashSet<Equation> andConjunct = new HashSet<>(equationSet);
					andConjunct.addAll(equationSetB);
					newElements.add(andConjunct);
				}
			}

			mEquations.clear();
			mEquations.addAll(newElements);
			removeImpossible(script);
		}

		public void and(final Equation newEquation, final ManagedScript script) {
			if (mEquations.isEmpty()) {
				mEquations.add(new HashSet<>());
			}

			final Set<Set<Equation>> newElements = new HashSet<>();

			// Distributivity, add the equation to every conjunct.
			for (final Set<Equation> equationSet : mEquations) {
				final HashSet<Equation> andConjunct = new HashSet<>(equationSet);
				andConjunct.add(newEquation);
				newElements.add(andConjunct);
			}

			mEquations.clear();
			mEquations.addAll(newElements);
			removeImpossible(script);
		}

		public void or(final Equations equationsB, final ManagedScript script) {
			mEquations.addAll(equationsB.mEquations);
			removeImpossible(script);
		}

		public void or(final Equation newEquation, final ManagedScript script) {
			// Add new and conjunct that only contains the equation
			final HashSet<Equation> andConjunct = new HashSet<>();
			andConjunct.add(newEquation);
			mEquations.add(andConjunct);
			removeImpossible(script);
		}

		private void removeImpossible(final ManagedScript script) {
			final Set<Set<Equation>> unsatisfiable = new HashSet<>();
			for (final Set<Equation> equationSet : mEquations) {
				if (equationSet.size() < 2) {
					continue;
				}
				final List<Term> smtEquations = equationSet.stream()
						.map(equation -> equation.toTerm(script.getScript())).toList();
				final Term test = SmtUtils.and(script.getScript(), smtEquations);

				if (test.equals(script.getScript().getTheory().mFalse)
						|| SmtUtils.checkEquivalence(test, script.getScript().getTheory().mFalse, script.getScript())
								.equals(LBool.UNSAT)) {
					unsatisfiable.add(equationSet);
				}
			}
			mEquations.removeAll(unsatisfiable);
		}

		public void negate(final ManagedScript script) {
			final Equations out = new Equations();

			for (final Set<Equation> equationSet : mEquations) {
				if (equationSet.isEmpty()) {
					continue;
				}
				// Get the negated term, negation turns the dnf into a cnf, this is a conjunction of disjunctions.
				final Set<Equation> negatedSet = new HashSet<>(
						equationSet.stream().map((equation) -> equation.negate()).toList());

				// Create dnf from cnf by using the defined and / or operations that handle distributivity.
				final Iterator<Equation> iter = negatedSet.iterator();
				final Equations disjunct = new Equations(iter.next());
				while (iter.hasNext()) {
					disjunct.or(iter.next(), script);
				}
				out.and(disjunct, script);
			}

			mEquations.clear();
			mEquations.addAll(out.mEquations);
		}

		/**
		 * Removes all equalities that do not contain Out- or Aux-Vars.
		 *
		 * @param term
		 * @return
		 */
		public void removeGuardEquations(final UnmodifiableTransFormula formula) {
			final HashSet<TermVariable> assignableVars = new HashSet<>(formula.getAuxVars());
			final Collection<TermVariable> inVars = formula.getInVars().values();

			assignableVars
					.addAll(formula.getOutVars().values().stream().filter((entry) -> !inVars.contains(entry)).toList());

			for (final Set<Equation> equationSet : mEquations) {
				final HashSet<Equation> guardTerms = new HashSet<>();
				for (final Equation equation : equationSet) {
					if (!equation.getFreeVars().stream().anyMatch((var) -> assignableVars.contains(var))) {
						// if exists var that is in the assignable vars
						// => term has importance for updates
						// otherwise: delete from equations
						guardTerms.add(equation);
					}
				}
				equationSet.removeAll(guardTerms);
			}
		}

		public SolvedEquations solveForAllVars(final Script script) {
			final Set<Set<SolvedEquation>> outData = new HashSet<>();
			for (final Set<Equation> equationSet : mEquations) {
				final HashSet<SolvedEquation> solvedEquations = new HashSet<>();
				for (final Equation equation : equationSet) {
					solvedEquations.addAll(equation.solveForVars(script));
				}
				outData.add(solvedEquations);
			}
			return new SolvedEquations(outData);
		}

		public record SolvedEquations(Set<Set<SolvedEquation>> equations) {
			@Override
			public String toString() {
				final StringBuilder builder = new StringBuilder("or (\n");
				for (final Set<SolvedEquation> equationSet : equations) {
					builder.append("\tand(\n");
					for (final Equation equation : equationSet) {
						builder.append("\t\t").append(equation.toString()).append("\n");
					}
					builder.append("\t)\n");
				}
				return builder.append(")").toString();
			}

			/** */
			public SolvedEquations getGuardSubset(final UnmodifiableTransFormula formula) {
				final Collection<TermVariable> inVars = formula.getInVars().values();

				return new SolvedEquations(
						new HashSet<>(equations.stream()
								.map(equationSet -> new HashSet<>(equationSet.stream()
										.filter(equation -> inVars.containsAll(equation.getFreeVars())).toList()))
								.toList()));
			}
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder("or (\n");
			for (final Set<Equation> equationSet : mEquations) {
				builder.append("\tand(\n");
				for (final Equation equation : equationSet) {
					builder.append("\t\t").append(equation.toString()).append("\n");
				}
				builder.append("\t)\n");
			}
			return builder.append(")").toString();
		}
	}

	public static Equations extract(final Term term, final ManagedScript script) {
		switch (term) {
		case final ApplicationTerm at:
			return extractAppliactionTerm(at, script);
		default:
			return new Equations();
		}
	}

	public static Equations extractAppliactionTerm(final ApplicationTerm term, final ManagedScript script) {
		Equations out;
		System.out.println(term.toStringDirect());
		switch (term.getFunction().getName()) {
		case SMTLIBConstants.OR:
			out = new Equations();
			for (final Term subTerm : term.getParameters()) {
				final Equation booleanEq = getBooleanEquivalence(subTerm);
				if (booleanEq != null) {
					out.or(booleanEq, script);
				} else {
					out.or(extract(subTerm, script), script);
				}
			}
			break;
		case SMTLIBConstants.AND:
			out = new Equations();
			for (final Term subTerm : term.getParameters()) {
				final Equation booleanEq = getBooleanEquivalence(subTerm);
				if (booleanEq != null) {
					out.and(booleanEq, script);
				} else {
					out.and(extract(subTerm, script), script);
				}
			}
			break;
		case SMTLIBConstants.EQUALS:
			out = addEquations(term.getParameters(), RelationSymbol.EQ, script);
			break;
		case SMTLIBConstants.LEQ:
			out = addEquations(term.getParameters(), RelationSymbol.LEQ, script);
			break;
		case SMTLIBConstants.LT:
			out = addEquations(term.getParameters(), RelationSymbol.LESS, script);
			break;
		case SMTLIBConstants.GEQ:
			out = addEquations(term.getParameters(), RelationSymbol.GEQ, script);
			break;
		case SMTLIBConstants.GT:
			out = addEquations(term.getParameters(), RelationSymbol.GREATER, script);
			break;
		case SMTLIBConstants.NOT:
			out = extract(term.getParameters()[0], script);
			out.negate(script);
			break;
		default:
			out = new Equations();
			break;
		}
		return out;
	}

	public static Equation getBooleanEquivalence(Term term) {
		ApplicationTerm element;
		if (term instanceof final ApplicationTerm at) {
			if (!at.getFunction().getName().equals(SMTLIBConstants.NOT)) {
				return null;
			}

			element = term.getTheory().mFalse;
			term = at.getParameters()[0];
		} else {
			element = term.getTheory().mTrue;
		}

		if (term instanceof final TermVariable tv) {
			// we have a variable term which means we return the equation var = true / false.
			return new SolvedEquation(RelationSymbol.EQ, tv, element);
		}
		if (term instanceof final ApplicationTerm subAT
				&& subAT.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			// we have a select term which means we return the equation select array key = true / false.
			return new Equation(RelationSymbol.EQ, subAT, element);
		}
		return null;
	}

	private static Equations addEquations(final Term[] subTerms, final RelationSymbol relation,
			final ManagedScript script) {
		final Equations out = new Equations();// new Equation(relation, subTerms[0], subTerms[1]));

		for (int i = 1; i < subTerms.length; i++) {
			out.and(new Equation(relation, subTerms[i - 1], subTerms[i]), script);
		}

		return out;
	}
}
