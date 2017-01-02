package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunction;
import de.uni_freiburg.informatik.ultimate.lassoranker.termination.AffineFunctionGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;


/**
 * Class represents an abstract linear invariant pattern, that consists of
 * - a strict/non-strict linear inequality that is defined for 
 * - a set of variables, and
 * - each variable is associated with a coefficient.
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public abstract class AbstractLinearInvariantPattern {
	
	protected AffineFunctionGenerator mFunctionGenerator;
	protected boolean mStrictInequality;
	
	protected Set<IProgramVar> mVariablesOfThisPattern;
	
	protected AbstractLinearInvariantPattern () {
		
	}
	
	public AbstractLinearInvariantPattern (final Script solver,
			final Set<IProgramVar> variables, final String prefix,
			final boolean strict) {
		mFunctionGenerator = new AffineFunctionGenerator(solver, variables, prefix);
		mStrictInequality = strict;
		mVariablesOfThisPattern = variables;
	}
	
	/**
	 * 
	 * @return
	 */
	public Set<IProgramVar> getVariables() {
		return mVariablesOfThisPattern;
	}
	
	/**
	 * Returns a collection of terms representing one generated variable each.
	 * 
	 * Generated variables are coefficients for {@link IProgramVar}s and the
	 * constant term.
	 * 
	 * @return collection of all variables
	 */
	public Collection<Term> getCoefficients () {
		return mFunctionGenerator.getCoefficients();
	}
	
	/**
	 * Returns whether or not this pattern represents a strict term.
	 * 
	 * @return true iff the pattern represents a strict term
	 */
	public boolean isStrict() {
		return mStrictInequality;
	}
	
	public abstract AffineFunction getAffineFunction(final Map<Term, Rational> valuation);
	
	public abstract LinearInequality getLinearInequality(final Map<IProgramVar, Term> map);
	
}
