package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
//import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf.Dnf;

/**
 * This strategy computes invariant patterns (templates) depending on the location
 * (node of the graph), the current round and dimensions strategy (see {@link AbstractTemplateIncreasingDimensionsStrategy}).
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public abstract class LocationDependentLinearInequalityInvariantPatternStrategy
		implements ILinearInequalityInvariantPatternStrategy<Dnf<AbstractLinearInvariantPattern>> {

	private final int maxRounds;
	protected final Set<IProgramVar> mAllProgramVariables;
	protected int mPrefixCounter;
	protected Map<IcfgLocation, Set<Term>> mLoc2PatternCoefficents;
	protected boolean mAlwaysStrictAndNonStrictCopies;
	protected boolean mUseStrictInequalitiesAlternatingly;
	protected AbstractTemplateIncreasingDimensionsStrategy mDimensionsStrategy;

	/**
	 * Generates a simple linear inequality invariant pattern strategy.
	 *
	 * @param maxRounds
	 *            maximal number of rounds to be announced by
	 *            {@link #getMaxRounds()}.
	 * @param allProgramVariables
	 */
	public LocationDependentLinearInequalityInvariantPatternStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat,
			final int maxRounds, final Set<IProgramVar> allProgramVariables, final boolean alwaysStrictAndNonStrictCopies,
			final boolean useStrictInequalitiesAlternatingly) {
		mDimensionsStrategy = dimensionsStrat;
		this.maxRounds = maxRounds;
		mAllProgramVariables = allProgramVariables;
		mPrefixCounter = 0;
		mLoc2PatternCoefficents = new HashMap<>();
		mAlwaysStrictAndNonStrictCopies = alwaysStrictAndNonStrictCopies;
		mUseStrictInequalitiesAlternatingly = useStrictInequalitiesAlternatingly;
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix) {
		final int[] dimensions = getDimensions(location, round);
		final Set<Term> patternCoefficients = new HashSet<>();
		// Build invariant pattern
		final Dnf<AbstractLinearInvariantPattern> disjunction = new Dnf<>(dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<AbstractLinearInvariantPattern> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				boolean[] invariantPatternCopies = new boolean[] { false };
				if (mUseStrictInequalitiesAlternatingly) {
					// if it is an odd conjunct, then construct a strict inequality
					if (j % 2 == 1) {
						invariantPatternCopies = new boolean[] { true };
					}
				}
				if (mAlwaysStrictAndNonStrictCopies) {
					invariantPatternCopies = new boolean[] { false, true };
				}
				for (final boolean strict : invariantPatternCopies) {
					final LinearPatternBase inequality = new LinearPatternBase (
							solver, getPatternVariablesForLocation(location, round), prefix + "_" + newPrefix(), strict);
					conjunction.add(inequality);
					// Add the coefficients of the inequality to our set of pattern coefficients
					patternCoefficients.addAll(inequality.getCoefficients());
				}
			}
			disjunction.add(conjunction);
		}
		mLoc2PatternCoefficents.put(location, patternCoefficients);
		return disjunction;
	}

	@Override
	public void setNumOfConjunctsForLocation(final IcfgLocation location, final int numOfConjuncts) {
//		mLoc2MaxNumOfConjuncts.put(location, maxNumOfConjuncts);
		throw new UnsupportedOperationException("not yet implemented");
	}

	@Override
	public void setNumOfDisjunctsForLocation(final IcfgLocation location, final int numOfDisjuncts) {
		throw new UnsupportedOperationException("not yet implemented");
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
	public int[] getDimensions(final IcfgLocation location, final int round) {
		return mDimensionsStrategy.getDimensions(location, round);
	}

	@Override
	public void resetSettings() {
		mPrefixCounter = 0;
	}

	protected String newPrefix() {
		return Integer.toString(mPrefixCounter++);
	}

	@Override
	public Set<Term> getPatternCoefficientsForLocation(final IcfgLocation location) {
		assert mLoc2PatternCoefficents.containsKey(location) : "No coefficients available for the location: " + location;
		return Collections.unmodifiableSet(mLoc2PatternCoefficents.get(location));
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getPatternForTransition(final IcfgEdge transition, final int round,
			final Script solver, final String prefix) {
		throw new UnsupportedOperationException();
	}

	@Override
	public Set<Term> getIntegerCoefficientsForTransition(final IcfgEdge transition) {
		throw new UnsupportedOperationException();
	}
}
