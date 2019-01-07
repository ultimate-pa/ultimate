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
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf.Dnf;


/**
 * This strategy constructs invariant patterns using those program variables which have been previously in the unsatisfiable core.
 * If it is the first iteration, then either all program variables or only the live variables are used for the pattern.
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class VarsInUnsatCoreStrategy extends LiveVariablesStrategy {

	private final Map<IcfgLocation, Set<IProgramVar>> mLocations2PatternVariables;

	public VarsInUnsatCoreStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat,
			final int maxRounds, final Set<IProgramVar> allProgramVariables,
			final Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables, final boolean alwaysStrictAndNonStrictCopies,
			final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				locs2LiveVariables, alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLocations2PatternVariables = new HashMap<>();
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(final IcfgLocation location,
			final int round, final Script solver, final String prefix, final Set<IProgramVar> varsFromUnsatCore) {
		assert super.mLoc2PatternCoefficents != null : "Map mLoc2PatternCoefficents must not be null!";
		final Set<Term> patternCoefficients = new HashSet<>();
		final Set<IProgramVar> varsForThisPattern = new HashSet<>(getPatternVariablesForLocation(location, round));
		if (!varsFromUnsatCore.containsAll(varsForThisPattern)) {
			varsForThisPattern.addAll(varsFromUnsatCore);
		}
		// Put variables used for this pattern into the map
		mLocations2PatternVariables.put(location, varsForThisPattern);
		final int[] dimensions = getDimensions(location, round);
		// Build invariant pattern
		final Dnf<AbstractLinearInvariantPattern> disjunction = new Dnf<>(dimensions[0]);
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
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location, final int round) {
		if (mLocations2PatternVariables.containsKey(location)) {
			return Collections.unmodifiableSet(mLocations2PatternVariables.get(location));
		} else if (super.mLocations2LiveVariables != null) {
			return Collections.unmodifiableSet(super.mLocations2LiveVariables.get(location));
		} else {
			return Collections.unmodifiableSet(super.mAllProgramVariables);
		}
	}

}
