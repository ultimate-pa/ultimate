package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

/**
 * A processor for invariant patterns. The processor generates invariant
 * patterns for each {@link ControlFlowGraph.Location} in an
 * {@link ControlFlowGraph}, and solves the system of all corresponding
 * {@link InvariantTransitionPredicate}s.
 * 
 * For each round, methods are invoked in the following order:
 * <ol>
 *   <li>{@link #startRound(int)}</li>
 *   <li>
 *     {@link #getInvariantPatternForLocation(Location, int)} for all locations
 *   </li>
 *   <li>{@link #hasValidConfiguration(Collection, int)}</li>
 * </ol>
 * 
 * @param <IPT>
 *            Invariant Pattern Type: Type used for invariant patterns
 */
public interface IInvariantPatternProcessor<IPT> {
	
	/**
	 * Called when a new round is entered.
	 * 
	 * @param round
	 */
	public void startRound(final int round);

	/**
	 * Returns an invariant pattern for the given location.
	 * 
	 * @param location
	 *            the location to generate an invariant pattern for
	 * @param round
	 *            attempt number, initialized with 0 and increased on each
	 *            attempt; see {@link #getMaxRounds()}
	 * @return invariant pattern for location
	 */
	public IPT getInvariantPatternForLocation(final Location location,
			final int round);

	/**
	 * Attempts to find a valid configuration for all pattern variables,
	 * satisfying any of the given {@link InvariantTransitionPredicate}s.
	 * 
	 * @param predicates
	 *            the predicates to satisfy
	 * @param round
	 *            attempt number, initialized with 0 and increased on each
	 *            attempt; see {@link #getMaxRounds()}
	 * @return true if a valid configuration pattern has been found, false
	 *         otherwise.
	 */
	public boolean hasValidConfiguration(
			final Collection<InvariantTransitionPredicate<IPT>> predicates,
			final int round);
	
	/**
	 * Applies the configuration found with
	 * {@link #hasValidConfiguration(Collection, int)} to a given invariant
	 * pattern.
	 * 
	 * The behaviour of this method is undefined, when the last call to
	 * {@link #hasValidConfiguration(Collection, int)} returned false or if
	 * {@link #hasValidConfiguration(Collection, int)} has not yet been called
	 * at all.
	 * 
	 * @param pattern the pattern to apply the configuration to
	 * @return the predicate representing the invariant found
	 */
	public IPredicate applyConfiguration(IPT pattern);

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
