package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

/**
 * A processor for invariant patterns. The processor generates invariant
 * patterns for each {@link ControlFlowGraph.Location} in an
 * {@link ControlFlowGraph}, and solves the system of all corresponding
 * {@link InvariantTransitionPredicate}s.
 */
public interface IInvariantPatternProcessor {
	/**
	 * Returns an invariant pattern for the given location.
	 * 
	 * Invariant patterns are represented as {@link Term}s containing both
	 * program variables and pattern variables. See TODO for details on naming
	 * conventions.
	 * 
	 * @param location the location to generate an invariant pattern for
	 * @param round attempt number, initialized with 0 and increased on each
	 * attempt; see {@link #getMaxRounds()}
	 * @return invariant pattern for location
	 */
	public Term getInvariantPatternForLocation(final Location location,
			final int round);
	
	/**
	 * Returns a valid configuration for all pattern variables, satisfying all
	 * of the given {@link InvariantTransitionPredicate}s.
	 *  
	 * @param predicates the predicates to satisfy
	 * @param round attempt number, initialized with 0 and increased on each
	 * attempt; see {@link #getMaxRounds()}
	 * @return valid configuration satisfying all predicates, or null if no such
	 * configuration has been found.
	 */
	public Map<TermVariable, ConstantTerm> getValidConfiguration(
			final Collection<InvariantTransitionPredicate> predicates,
			final int round);
	
	/**
	 * Returns the maximal number of attempts to re-generate the invariant
	 * pattern map.
	 * 
	 * The round parameter will get for each integer between 0 and
	 * <code>getMaxRounds() - 1</code>.
	 * 
	 * @return maximal number of attempts to re-generate the invariant map
	 */
	public int getMaxRounds();
}
