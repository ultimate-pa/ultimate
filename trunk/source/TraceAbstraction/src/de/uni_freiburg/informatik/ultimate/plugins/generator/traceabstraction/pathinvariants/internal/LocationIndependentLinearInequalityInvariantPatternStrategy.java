/*
 * Copyright (C) 2015 Dirk Steinmetz
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * A simple {@link ILinearInequalityInvariantPatternStrategy}, generating
 * location-independent invariant patterns, each a disjunction composed of a
 * increasing number of conjunctions of a increasing number of inequalities over
 * all program variables.
 */
public abstract class LocationIndependentLinearInequalityInvariantPatternStrategy
		implements ILinearInequalityInvariantPatternStrategy<Collection<Collection<AbstractLinearInvariantPattern>>> {
	
	private final int maxRounds;
	protected final Set<IProgramVar> mAllProgramVariables;
	protected final Set<IProgramVar> mPatternVariables;
	protected int mPrefixCounter;
	protected Map<IcfgLocation, Set<Term>> mLoc2PatternCoefficents;
	private boolean mAlwaysStrictAndNonStrictCopies;
	private boolean mUseStrictInequalitiesAlternatingly;
	protected AbstractTemplateIncreasingDimensionsStrategy mDimensionsStrategy;
	
	/**
	 * Generates a simple linear inequality invariant pattern strategy.
	 * 
	 * @param maxRounds
	 *            maximal number of rounds to be announced by
	 *            {@link #getMaxRounds()}.
	 * @param patternVariables 
	 * @param allProgramVariables 
	 */
	public LocationIndependentLinearInequalityInvariantPatternStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat,
			final int maxRounds, Set<IProgramVar> allProgramVariables, Set<IProgramVar> patternVariables,
			boolean alwaysStrictAndNonStrictCopies, boolean useStrictInequalitiesAlternatingly) {
		mDimensionsStrategy = dimensionsStrat;
		this.maxRounds = maxRounds;
		mAllProgramVariables = allProgramVariables;
		mPatternVariables = patternVariables;
		mPrefixCounter = 0;
		mLoc2PatternCoefficents = new HashMap<>();
		mAlwaysStrictAndNonStrictCopies = alwaysStrictAndNonStrictCopies;
		mUseStrictInequalitiesAlternatingly = useStrictInequalitiesAlternatingly;
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int getMaxRounds() {
		return maxRounds;
	}
	
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location, int round, Script solver, String prefix) {
		Set<Term> patternCoefficients = new HashSet<>();
		final int[] dimensions = getDimensions(location, round);
		// Build invariant pattern
		final Collection<Collection<AbstractLinearInvariantPattern>> disjunction = new ArrayList<>(dimensions[0]);
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
	public Set<Term> getPatternCoefficientsForLocation(IcfgLocation location) {
		assert mLoc2PatternCoefficents.containsKey(location) : "No coefficients available for the location: " + location;
		return Collections.unmodifiableSet(mLoc2PatternCoefficents.get(location));
	}

	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location,
			int round, Script solver, String prefix, Set<IProgramVar> vars) {
		throw new UnsupportedOperationException("Location independent strategies do not support this kind of pattern construction.");
	}
	
	@Override
	public void setNumOfConjunctsForLocation(final IcfgLocation location, int maxNumOfConjuncts) {
		throw new UnsupportedOperationException("Location independent strategies do not support location-dependent pattern settings.");
	}
	@Override
	public void setNumOfDisjunctsForLocation(final IcfgLocation location, int maxNumOfDisjuncts) {
		throw new UnsupportedOperationException("Location independent strategies do not support location-dependent pattern settings.");
	}
	
	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round) {
		throw new UnsupportedOperationException("Location independent strategies do not support dynamic setting changes.");
	}
	
	@Override
	public void changePatternSettingForLocation(IcfgLocation location, final int round, Set<IcfgLocation> locationsInUnsatCore) {
		throw new UnsupportedOperationException("Location independent strategies do not support dynamic setting changes.");
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public int[] getDimensions(IcfgLocation location, int round) {
		return mDimensionsStrategy.getDimensions(location, round);
	}
	
	public void resetSettings() {
		mPrefixCounter = 0;
	}
	
	protected String newPrefix() {
		return Integer.toString(mPrefixCounter++);
	}

}
