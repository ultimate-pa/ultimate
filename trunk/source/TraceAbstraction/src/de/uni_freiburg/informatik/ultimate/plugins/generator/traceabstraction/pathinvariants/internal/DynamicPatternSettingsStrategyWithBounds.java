package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

public class DynamicPatternSettingsStrategyWithBounds extends DynamicPatternSettingsStrategy {
	protected Map<IcfgLocation, Integer> mLoc2MaxNumOfConjuncts;
	protected Map<IcfgLocation, Integer> mLoc2MaxNumOfDisjuncts;

	public DynamicPatternSettingsStrategyWithBounds(final TemplateDimensionsStrategy dimensionsStrat, int maxRounds, Set<IProgramVar> allProgramVariables, Map<IcfgLocation, Set<IProgramVar>> loc2LiveVariables,
			boolean alwaysStrictAndNonStrictCopies, boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLoc2MaxNumOfConjuncts = new HashMap<>();
		mLoc2MaxNumOfDisjuncts = new HashMap<>();
	}
	
	
	
	@Override
	public void setNumOfConjunctsForLocation(final IcfgLocation location, int numOfConjuncts) {
		mLoc2MaxNumOfConjuncts.put(location, numOfConjuncts);
	}
	
	public void setNumOfDisjunctsForLocation(final IcfgLocation location, int numOfDisjuncts) {
		mLoc2MaxNumOfDisjuncts.put(location, numOfDisjuncts);
	}
	
	
	@Override
	public Collection<Collection<AbstractLinearInvariantPattern>> getInvariantPatternForLocation(IcfgLocation location,
			int round, Script solver, String prefix) {
		PatternSetting ps;
		if (!mLoc2PatternSetting.containsKey(location)) {
			// Create new setting for this location
			Set<IProgramVar> varsForThisPattern = getPatternVariablesInitially(location);
			int numOfConjuncts = super.mDimensionsStrategy.getInitialConjuncts();
			int numOfDisjuncts = super.mDimensionsStrategy.getInitialDisjuncts();
			if (mLoc2MaxNumOfConjuncts.containsKey(location)) {
				numOfConjuncts = mLoc2MaxNumOfConjuncts.get(location);
			}
			if (mLoc2MaxNumOfDisjuncts.containsKey(location)) {
				numOfDisjuncts = mLoc2MaxNumOfDisjuncts.get(location);
			}
			ps = new PatternSetting(numOfDisjuncts, numOfConjuncts, varsForThisPattern);
			mLoc2PatternSetting.put(location, ps);
		} else {
			ps = mLoc2PatternSetting.get(location);
		}
		return constructInvariantPatternForSetting(location, ps, solver, prefix);
	}
}
