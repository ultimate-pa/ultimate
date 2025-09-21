package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This strategy maintains a global template level and increases it if it is reached by all locations. The template
 * setting for a given location is changed only if it has not reached the global template level, yet.
 */
public class DynamicPatternSettingsStrategyWithGlobalTemplateLevel extends DynamicPatternSettingsStrategy {
	private Pair<Integer, Integer> mCurrentGlobalTemplateLevel;

	public DynamicPatternSettingsStrategyWithGlobalTemplateLevel(
			final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, final int maxRounds,
			final Set<IProgramVar> allProgramVariables, final Map<IcfgLocation, Set<IProgramVar>> loc2LiveVariables,
			final boolean alwaysStrictAndNonStrictCopies, final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables, alwaysStrictAndNonStrictCopies,
				useStrictInequalitiesAlternatingly);
		mCurrentGlobalTemplateLevel =
				new Pair<>(dimensionsStrat.getInitialDisjuncts(), dimensionsStrat.getInitialConjuncts());
	}

	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round) {
		if (mLoc2PatternSetting.containsKey(location)) {
			final PatternSetting ps = mLoc2PatternSetting.get(location);
			// Change the template setting for the current location only if it is not at the global template level
			if (!mCurrentGlobalTemplateLevel.equals(new Pair<>(ps.getNumOfDisjuncts(), ps.getNumOfConjuncts()))) {
				ps.changeSetting(location, round);
			}
		}
	}

	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round,
			final Set<IcfgLocation> locationsInUnsatCore) {
		// TODO: The method allLocationsAtGlobalTemplateLevel should be called only once per round.
		if (allLocationsAtGlobalTemplateLevel(locationsInUnsatCore)) {
			changeGlobalTemplateLevel();
		}
		changePatternSettingForLocation(location, round);
	}

	private void changeGlobalTemplateLevel() {
		final int currentNumOfDisjuncts = mCurrentGlobalTemplateLevel.getFirst();
		int newNumOfDisjuncts = currentNumOfDisjuncts;
		final int currentNumOfConjuncts = mCurrentGlobalTemplateLevel.getSecond();
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
		mCurrentGlobalTemplateLevel = new Pair<>(newNumOfDisjuncts, newNumOfConjuncts);
	}

	private boolean allLocationsAtGlobalTemplateLevel(final Set<IcfgLocation> locations) {
		for (final IcfgLocation loc : locations) {
			if (mLoc2PatternSetting.containsKey(loc)) {
				final PatternSetting ps = mLoc2PatternSetting.get(loc);
				if (!mCurrentGlobalTemplateLevel.equals(new Pair<>(ps.getNumOfDisjuncts(), ps.getNumOfConjuncts()))) {
					return false;
				}
			}
		}
		return true;
	}
}
