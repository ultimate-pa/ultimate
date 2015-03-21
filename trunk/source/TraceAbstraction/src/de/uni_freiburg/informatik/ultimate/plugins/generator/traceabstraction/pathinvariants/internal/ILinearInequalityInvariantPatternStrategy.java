package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

/**
 * A strategy to generate invariant patterns composed of each a disjunction of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 * 
 * @see LinearInequalityInvariantPatternProcessor
 */
public interface ILinearInequalityInvariantPatternStrategy {

	/**
	 * Returns the number of elements in the outer disjunction and in each inner
	 * conjunction.
	 * 
	 * @param location
	 *            the location to generate an invariant pattern for
	 * @param rount
	 *            the round
	 * 
	 * @return Array with exactly two fields, the first one containing the
	 *         number of elements in the outer disjunction and the second one
	 *         containing the number of elements within each inner conjunction,
	 *         where each element means
	 *         "one strict inequality and one non-strict one".
	 */
	public int[] getDimensions(final Location location, final int round);

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
