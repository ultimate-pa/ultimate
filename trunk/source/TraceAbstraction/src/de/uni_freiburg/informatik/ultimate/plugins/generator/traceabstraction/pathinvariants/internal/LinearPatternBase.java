package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.lassoranker.variables.RankVar;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A class representing an (possibly strict) linear inequality over a set of
 * {@link RankVar}s. A DNF over these inequalities forms a pattern as used
 * within {@link LinearInequalityInvariantPatternProcessor}.
 */
public final class LinearPatternBase {
	private final AffineFunctionGenerator function;
	private final boolean strict;

	/**
	 * Creates a new linear inequality over a given set of {@link RankVar}s.
	 * 
	 * @param solver
	 *            the solver to generate new function symbols in (for
	 *            coefficients and constant term)
	 * @param variables
	 *            collection of variables
	 * @param prefix
	 *            unique prefix, which is not used by any other instance of this
	 *            class or other classes accessing the same solver
	 * @param strict
	 *            true iff a strict inequality is to be generated, false iff a
	 *            non-strict inequality is to be generated
	 */
	public LinearPatternBase(final Script solver,
			final Collection<RankVar> variables, final String prefix,
			boolean strict) {
		this.function = new AffineFunctionGenerator(solver, variables, prefix);
		this.strict = strict;
	}

	/**
	 * Returns a collection of terms representing one generated variable each.
	 * 
	 * Generated variables are coefficients for {@link RankVar}s and the
	 * constant term.
	 * 
	 * @return collection of all variables
	 */
	public Collection<Term> getVariables() {
		return function.getVariables();
	}

	/**
	 * Returns a linear inequality corresponding to this part of the invariant,
	 * when applied to a given {@link RankVar}-Mapping (that is, a map assigning
	 * a {@link Term} to each {@link RankVar} within the inequality represented
	 * by this class).
	 * 
	 * @param map
	 *            mapping to {@link Terms} to be used within the
	 *            {@link LinearInequality} generated
	 * @return linear inequality equivalent to the linear inequality represented
	 *         by this class, where each {@link RankVar} is replaced according
	 *         to the given mapping
	 */
	public LinearInequality getLinearInequality(final Map<RankVar, Term> map) {
		final LinearInequality inequality = function.generate(map);
		inequality.setStrict(strict);
		return inequality;
	}
	
	/**
	 * Returns whether or not this pattern represents a strict term.
	 * 
	 * @return true iff the pattern represents a strict term
	 */
	public boolean isStrict() {
		return strict;
	}
	
	public AffineFunction getAffineFunction(final Map<Term, Rational> valuation){
		return function.extractAffineFunction(valuation);
	}
}
