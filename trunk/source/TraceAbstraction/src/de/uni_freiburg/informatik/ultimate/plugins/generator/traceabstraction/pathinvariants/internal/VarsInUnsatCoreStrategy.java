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
 * This strategy constructs invariant patterns using those program variables which have been previously in the unsatisfiable core.
 * If it is the first iteration, then either all program variables or only the live variables are used for the pattern.
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class VarsInUnsatCoreStrategy extends LiveVariablesStrategy {
	
	private Map<IcfgLocation, Set<IProgramVar>> mLocations2PatternVariables;
	
	public VarsInUnsatCoreStrategy(final TemplateDimensionsStrategy dimensionsStrat,
			int maxRounds, Set<IProgramVar> allProgramVariables,
			Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables, boolean alwaysStrictAndNonStrictCopies,
			boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				locs2LiveVariables, alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLocations2PatternVariables = new HashMap<>();
	}

	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location,
			int round, Script solver, String prefix, Set<IProgramVar> varsFromUnsatCore) {
		assert super.mLoc2PatternCoefficents != null : "Map mLoc2PatternCoefficents must not be null!";
		Set<Term> patternCoefficients = new HashSet<>();
		Set<IProgramVar> varsForThisPattern = new HashSet<>(getPatternVariablesForLocation(location, round));
		if (!varsFromUnsatCore.containsAll(varsForThisPattern)) {
			varsForThisPattern.addAll(varsFromUnsatCore);
		}
		// Put variables used for this pattern into the map
		mLocations2PatternVariables.put(location, varsForThisPattern);
		final int[] dimensions = getDimensions(location, round);
		// Build invariant pattern
		final Collection<Collection<AbstractLinearInvariantPattern>> disjunction = new ArrayList<>(dimensions[0]);
		for (int i = 0; i < dimensions[0]; i++) {
			final Collection<AbstractLinearInvariantPattern> conjunction = new ArrayList<>(
					dimensions[1]);
			for (int j = 0; j < dimensions[1]; j++) {
				boolean[] invariantPatternCopies = new boolean[] { false };
				if (super.mUseStrictInequalitiesAlternatingly) {
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
							solver, varsForThisPattern, prefix + "_" + newPrefix(), strict);
					conjunction.add(inequality);
					// Add the coefficients of the inequality to our set of pattern coefficients
					patternCoefficients.addAll(inequality.getCoefficients());
				}
			}
			disjunction.add(conjunction);
		}
		super.mLoc2PatternCoefficents.put(location, patternCoefficients);
		return disjunction;
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(IcfgLocation location, int round) {
		if (mLocations2PatternVariables.containsKey(location)) {
			return Collections.unmodifiableSet(mLocations2PatternVariables.get(location));
		} else if (super.mLocations2LiveVariables != null) {
			return Collections.unmodifiableSet(super.mLocations2LiveVariables.get(location));
		} else {
			return Collections.unmodifiableSet(super.mAllProgramVariables);
		}
	}

}
