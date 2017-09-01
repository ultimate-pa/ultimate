package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This strategy maintains a global template level and increases it if it is reached by all locations.
 * The template setting for a given location is changed only if it has not reached the global template level, yet.
 */
public class DynamicPatternSettingsStrategyWithGlobalTemplateLevel extends DynamicPatternSettingsStrategy {
	private Pair<Integer, Integer> mCurrentGlobalTemplateLevel;

	public DynamicPatternSettingsStrategyWithGlobalTemplateLevel(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, int maxRounds, Set<IProgramVar> allProgramVariables, Map<IcfgLocation, Set<IProgramVar>> loc2LiveVariables,
			boolean alwaysStrictAndNonStrictCopies, boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mCurrentGlobalTemplateLevel = new Pair<Integer, Integer>(dimensionsStrat.getInitialDisjuncts(), dimensionsStrat.getInitialConjuncts());
	}
	
	@Override
	public void changePatternSettingForLocation(IcfgLocation location, final int round) {
		if (mLoc2PatternSetting.containsKey(location)) {
			PatternSetting ps = mLoc2PatternSetting.get(location);
			// Change the template setting for the current location only if it is not at the global template level
			if (!mCurrentGlobalTemplateLevel.equals(new Pair<Integer, Integer>(ps.getNumOfDisjuncts(), ps.getNumOfConjuncts()))) {
				ps.changeSetting(location, round);
			}
		} 		
	}

	@Override
	public void changePatternSettingForLocation(IcfgLocation location, final int round , Set<IcfgLocation> locationsInUnsatCore) {
		// TODO: The method allLocationsAtGlobalTemplateLevel should be called only once per round.
		if (allLocationsAtGlobalTemplateLevel(locationsInUnsatCore)) {
			changeGlobalTemplateLevel();
		}
		changePatternSettingForLocation(location, round);
	}
	
	private void changeGlobalTemplateLevel() {
		int currentNumOfDisjuncts = mCurrentGlobalTemplateLevel.getFirst();
		int newNumOfDisjuncts = currentNumOfDisjuncts;
		int currentNumOfConjuncts = mCurrentGlobalTemplateLevel.getSecond();
		int newNumOfConjuncts = currentNumOfConjuncts;
		if (currentNumOfConjuncts < 3) {
			newNumOfConjuncts = currentNumOfConjuncts + 1;

		} else if (currentNumOfDisjuncts < 2) {
			newNumOfDisjuncts = currentNumOfDisjuncts + 1;
		} else {
			if (currentNumOfConjuncts < 4) {
				newNumOfConjuncts = currentNumOfConjuncts + 1;
			} else {
				newNumOfDisjuncts = currentNumOfDisjuncts + 1;
				newNumOfConjuncts = currentNumOfConjuncts + 1;
			}
		}
		mCurrentGlobalTemplateLevel = new Pair<Integer, Integer>(newNumOfDisjuncts, newNumOfConjuncts);
	}
	
	private boolean allLocationsAtGlobalTemplateLevel(Set<IcfgLocation> locations) {
		for (IcfgLocation loc : locations) {
			if (mLoc2PatternSetting.containsKey(loc)) {
				PatternSetting ps = mLoc2PatternSetting.get(loc);
				if (!mCurrentGlobalTemplateLevel.equals(new Pair<Integer, Integer>(ps.getNumOfDisjuncts(), ps.getNumOfConjuncts()))) {
					return false;
				}
			}
		}
		return true;
	}
}
