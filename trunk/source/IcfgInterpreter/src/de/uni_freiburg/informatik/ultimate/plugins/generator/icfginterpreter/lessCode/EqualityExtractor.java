package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.UnmodifiableTransFormula;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.binaryrelation.RelationSymbol;
import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Equation.SolvedEquation;

public class EqualityExtractor {
	public static class Equations {
		private final Set<Equation> mEquations;

		public Equations(final Set<Equation> equations) {
			mEquations = equations;
		}

		protected Equations(final Equation equation) {
			mEquations = new HashSet<>();
			mEquations.add(equation);
		}

		public Equations() {
			this(new HashSet<>());
		}

		public void and(final Equations equationsB) {
			mEquations.addAll(equationsB.mEquations);
		}

		public void and(final Equation newEquation) {
			mEquations.add(newEquation);
		}

		public Set<SolvedEquation> solveForAllVars(final Script script) {
			final Set<SolvedEquation> outData = new HashSet<>();
			for (final Equation equation : mEquations) {
				outData.addAll(equation.solveForAllVars(script));
			}
			return outData;
		}

		/**
		 * Solve all equations for all contained out vars.
		 *
		 * @param script
		 * @return
		 */
		public Set<SolvedEquation> solveForRelevantVars(final Script script, final UnmodifiableTransFormula formula) {
			final Set<SolvedEquation> outData = new HashSet<>();
			final Set<Term> outVars = Set.copyOf(formula.getOutVars().values());
			final Set<Term> inVars = Set.copyOf(formula.getInVars().values());
			final Set<Term> assignableOutVars =
					Set.copyOf(outVars.stream().filter(outVar -> !inVars.contains(outVar)).toList());
			final Set<Term> auxVars = Set.copyOf(formula.getAuxVars());

			for (final Equation equation : mEquations) {
				// Solve the equation for all out variables that can change / are not constant
				outData.addAll(equation.solveForVars(script, assignableOutVars));
				final Set<TermVariable> freeVars = equation.getFreeVars();
				if (assignableOutVars.stream().noneMatch(freeVars::contains)) {
					// We also solve for aux vars if no assignable out var is contained. ()
					outData.addAll(equation.solveForVars(script, auxVars));
				}
			}
			return outData;
		}

		@Override
		public String toString() {
			final StringBuilder builder = new StringBuilder();
			for (final Equation equation : mEquations) {
				builder.append("\t").append(equation.toString()).append("\n");
			}
			return builder.toString().stripTrailing();
		}

		public Set<Equation> getEquations() {
			return mEquations;
		}
	}

	public static Equations extract(final Term term, final Script script, final UnmodifiableTransFormula formula,
			final ILogger logger) {
		switch (term) {
		case final ApplicationTerm at:
			return extractApplicationTerm(at, script, formula, logger);
		case final TermVariable tv:
			if (tv.getSort().getName().equals(SMTLIBConstants.BOOL)) {
				return new Equations(new Equation(RelationSymbol.EQ, tv, script.getTheory().mTrue));
			}
			break;
		default:
			break;
		}
		return new Equations();
	}

	public static class EdgeUntranslatableError extends AssertionError {
		private static final long serialVersionUID = 1L;
	}

	public static Equations extractApplicationTerm(final ApplicationTerm term, final Script script,
			final UnmodifiableTransFormula formula, final ILogger logger) {
		Equations out;
		switch (term.getFunction().getName()) {
		case SMTLIBConstants.OR:

			final List<TermVariable> outVars = formula.getOutVars().entrySet().stream()
					.filter(entry -> formula.getAssignedVars().contains(entry.getKey())).map(Entry::getValue).toList();

			if (Arrays.asList(term.getFreeVars()).stream().anyMatch(outVars::contains)) {
				// This term contains information that is needed in updates.
				logger.error("This plug-in does not handle or terms nested in other terms.\n"
						+ "Try using SingleStatement in your Icfg / Cfg Builder settings.\nOffending Term:\n"
						+ term.toStringDirect() + "\nof Transition\n" + formula.toStringDirect());
				throw new EdgeUntranslatableError();
			}
			// It's just guards, continue operation
			out = new Equations();
			break;

		case SMTLIBConstants.AND:
			out = new Equations();
			for (final Term subTerm : term.getParameters()) {
				final Equation booleanEq = getBooleanEquivalence(subTerm);
				if (booleanEq != null) {
					out.and(booleanEq);
				} else {
					out.and(extract(subTerm, script, formula, logger));
				}
			}
			break;
		case SMTLIBConstants.EQUALS:
			out = addEquations(term.getParameters(), RelationSymbol.EQ);
			break;
		case SMTLIBConstants.LEQ:
			out = addEquations(term.getParameters(), RelationSymbol.LEQ);
			break;
		case SMTLIBConstants.LT:
			out = addEquations(term.getParameters(), RelationSymbol.LESS);
			break;
		case SMTLIBConstants.GEQ:
			out = addEquations(term.getParameters(), RelationSymbol.GEQ);
			break;
		case SMTLIBConstants.GT:
			out = addEquations(term.getParameters(), RelationSymbol.GREATER);
			break;
		case SMTLIBConstants.NOT:
			final Set<Equation> eqs = extract(term.getParameters()[0], script, formula, logger).getEquations();
			if (eqs.size() == 1) {
				final Equation equation = eqs.iterator().next().negate();
				out = new Equations(equation);
			} else {
				out = new Equations();
			}
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
			return new Equation(RelationSymbol.EQ, tv, element);
		}
		if (term instanceof final ApplicationTerm subAT
				&& subAT.getFunction().getName().equals(SMTLIBConstants.SELECT)) {
			// we have a select term which means we return the equation select array key = true / false.
			return new Equation(RelationSymbol.EQ, subAT, element);
		}
		return null;
	}

	private static Equations addEquations(final Term[] subTerms, final RelationSymbol relation) {
		final Equations out = new Equations();

		for (int i = 1; i < subTerms.length; i++) {
			out.and(new Equation(relation, subTerms[i - 1], subTerms[i]));
		}

		return out;
	}
}
