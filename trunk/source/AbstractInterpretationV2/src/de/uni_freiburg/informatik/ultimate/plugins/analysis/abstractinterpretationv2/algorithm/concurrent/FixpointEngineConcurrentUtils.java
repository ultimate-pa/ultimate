package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class FixpointEngineConcurrentUtils {
	private FixpointEngineConcurrentUtils() {
	}

	public static <STATE extends IAbstractState<STATE>> STATE unionOnSharedVariables(final STATE state1,
			final STATE state2) {
		final Set<IProgramVarOrConst> sharedVars =
				DataStructureUtils.intersection(state1.getVariables(), state2.getVariables());
		final STATE unionOnSharedVars =
				projectOnVariables(state1, sharedVars).union(projectOnVariables(state2, sharedVars));
		final STATE result = state1.patch(unionOnSharedVars);
		final Set<IProgramVarOrConst> state2ExclusiveVars =
				DataStructureUtils.difference(state2.getVariables(), state1.getVariables());
		if (!state2ExclusiveVars.isEmpty()) {
			return result.patch(projectOnVariables(state2, state2ExclusiveVars));
		}
		return result;
	}

	private static <STATE extends IAbstractState<STATE>> STATE projectOnVariables(final STATE state,
			final Set<IProgramVarOrConst> vars) {
		return state.removeVariables(DataStructureUtils.difference(state.getVariables(), vars));
	}
}
