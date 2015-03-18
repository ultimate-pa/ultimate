package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal.ControlFlowGraph.Location;

/**
 * A simple {@link ILinearInequalityInvariantPatternStrategy}, generating
 * location-independent invariant patterns, each a disjunction composed of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 */
public final class LocationIndependentLinearInequalityInvariantPatternStrategy
		implements ILinearInequalityInvariantPatternStrategy {

	private final int baseDisjuncts;
	private final int baseConjuncts;
	private final int disjunctsPerRound;
	private final int conjunctsPerRound;
	private final int maxRounds;

	/**
	 * Generates a simple linear inequality invariant pattern strategy.
	 * 
	 * @param baseDisjuncts
	 *            number of conjunctions within the outer disjunction in the
	 *            pattern, first iteration
	 * @param baseConjuncts
	 *            number of inequalities within each conjunction in the pattern,
	 *            first iteration
	 * @param disjunctsPerRound
	 *            number of conjunctions within the outer disjunction added
	 *            after each round
	 * @param conjunctsPerRound
	 *            number of inequalities within each conjunction added after
	 *            each round
	 * @param maxRounds
	 *            maximal number of rounds to be announced by
	 *            {@link #getMaxRounds()}.
	 */
	public LocationIndependentLinearInequalityInvariantPatternStrategy(
			final int baseDisjuncts, final int baseConjuncts,
			final int disjunctsPerRound, final int conjunctsPerRound,
			final int maxRounds) {
		this.baseConjuncts = baseConjuncts;
		this.baseDisjuncts = baseDisjuncts;
		this.disjunctsPerRound = disjunctsPerRound;
		this.conjunctsPerRound = conjunctsPerRound;
		this.maxRounds = maxRounds;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int[] getDimensions(final Location location, final int round) {
		return new int[] { baseDisjuncts + round * disjunctsPerRound,
				baseConjuncts + round * conjunctsPerRound };
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return maxRounds;
	}

}
