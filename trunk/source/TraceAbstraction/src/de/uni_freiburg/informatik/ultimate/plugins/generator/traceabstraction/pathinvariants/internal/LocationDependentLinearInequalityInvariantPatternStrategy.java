package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
//import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * 
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public abstract class LocationDependentLinearInequalityInvariantPatternStrategy
		implements ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> {
	
	private final int baseDisjuncts;
	private final int baseConjuncts;
	private final int disjunctsPerRound;
	private final int conjunctsPerRound;
	private final int maxRounds;
	protected final Set<IProgramVar> mAllProgramVariables;
	protected int mPrefixCounter;

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
	 * @param allProgramVariables 
	 */
	public LocationDependentLinearInequalityInvariantPatternStrategy(
			final int baseDisjuncts, final int baseConjuncts,
			final int disjunctsPerRound, final int conjunctsPerRound,
			final int maxRounds, Set<IProgramVar> allProgramVariables) {
		this.baseConjuncts = baseConjuncts;
		this.baseDisjuncts = baseDisjuncts;
		this.disjunctsPerRound = disjunctsPerRound;
		this.conjunctsPerRound = conjunctsPerRound;
		this.maxRounds = maxRounds;
		mAllProgramVariables = allProgramVariables;
		mPrefixCounter = 0;
	}

	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location, int round, Script solver, String prefix) {
		final int[] dimensions = getDimensions(location, round);
		// Build invariant pattern
		final Collection<Collection<AbstractLinearInvariantPattern>> disjunction = new ArrayList<>(dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<AbstractLinearInvariantPattern> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				final boolean[] invariantPatternCopies;
					invariantPatternCopies = new boolean[] { false };
				for (final boolean strict : invariantPatternCopies) {
					final LinearPatternBase inequality = new LinearPatternBase (
							solver, getPatternVariablesForLocation(location, round), prefix + "_" + newPrefix(), strict);
					conjunction.add(inequality);
				}
			}
			disjunction.add(conjunction);
		}
		return disjunction;
	}
	

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return maxRounds;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int[] getDimensions(IcfgLocation location, int round) {
		return new int[] { baseDisjuncts + round * disjunctsPerRound,
				baseConjuncts + round * conjunctsPerRound };
		// 2015-10-27: Use the following instead to obtain two disjuncts
		// consisting of one strict-nonstrict conjunction pair each. 
//		return new int[] { 2, 1};
	}
	
	public void resetSettings() {
		mPrefixCounter = 0;
	}
	
	protected String newPrefix() {
		return Integer.toString(mPrefixCounter++);
	}

}
