package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.pathinvariants.internal;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
//import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.xnf.Dnf;

/**
 * This strategy constructs invariant patterns using those program variables which are <i> live </i> at the given
 * location.
 *
 * @author Betim Musa <musab@informatik.uni-freiburg.de>
 *
 */
public class LiveVariablesStrategy extends LocationDependentLinearInequalityInvariantPatternStrategy {

	protected Map<IcfgLocation, Set<IProgramVar>> mLocations2LiveVariables;

	public LiveVariablesStrategy(final AbstractTemplateIncreasingDimensionsStrategy dimensionsStrat, final int maxRounds, final Set<IProgramVar> allProgramVariables,
			final Map<IcfgLocation, Set<IProgramVar>> locs2LiveVariables,
			final boolean alwaysStrictAndNonStrictCopies,
			final boolean useStrictInequalitiesAlternatingly) {
		super(dimensionsStrat, maxRounds, allProgramVariables,
				alwaysStrictAndNonStrictCopies, useStrictInequalitiesAlternatingly);
		mLocations2LiveVariables = locs2LiveVariables;
	}

	@Override
	public Set<IProgramVar> getPatternVariablesForLocation(final IcfgLocation location, final int round) {
		final Set<IProgramVar> liveVars = mLocations2LiveVariables.get(location);
		if (liveVars == null) {
			return Collections.emptySet();
		}
		return Collections.unmodifiableSet(liveVars);
	}

	@Override
	public Dnf<AbstractLinearInvariantPattern> getInvariantPatternForLocation(
			final IcfgLocation location, final int round, final Script solver, final String prefix,
			final Set<IProgramVar> vars) {
		throw new UnsupportedOperationException(
				"LiveVariablesStrategy does not support this kind of pattern construction.");
	}

	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round) {
		throw new UnsupportedOperationException("LiveVariablesStrategy does not support dynamic setting changes.");
	}

	@Override
	public void changePatternSettingForLocation(final IcfgLocation location, final int round , final Set<IcfgLocation> locationsInUnsatCore) {
		throw new UnsupportedOperationException("LiveVariablesStrategy does not support dynamic setting changes.");
	}

}
