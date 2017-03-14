package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * For each location each inequality pattern contains all program variables.
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class AllProgramVariablesStrategy extends LocationIndependentLinearInequalityInvariantPatternStrategy {
	
	public AllProgramVariablesStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, int maxRounds, Set<IProgramVar> allProgramVariables, Set<IProgramVar> patternVariables,
			boolean alwaysStrictAndNonStrictCopies, boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables, patternVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(IcfgLocation location, int round) {
		return Collections.unmodifiableSet(mAllProgramVariables);
	}
}
