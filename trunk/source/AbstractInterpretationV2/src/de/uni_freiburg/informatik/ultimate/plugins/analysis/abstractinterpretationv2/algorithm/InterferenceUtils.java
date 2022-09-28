package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceUtils {
	private InterferenceUtils() {
	}

	// TODO: Does this also work for edge cases (top/bottom states)?
	public static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE> computeStateWithInterferences(
			final DisjunctiveAbstractState<STATE> state, final DisjunctiveAbstractState<STATE> interferingState) {
		final Set<IProgramVarOrConst> sharedVars =
				DataStructureUtils.intersection(interferingState.getVariables(), state.getVariables());
		final DisjunctiveAbstractState<STATE> unionOnSharedVars =
				keepVariables(state, sharedVars).union(keepVariables(interferingState, sharedVars));
		return state.patch(unionOnSharedVars);
	}

	private static <STATE extends IAbstractState<STATE>> DisjunctiveAbstractState<STATE>
			keepVariables(final DisjunctiveAbstractState<STATE> state, final Set<IProgramVarOrConst> vars) {
		final Set<IProgramVarOrConst> varsToRemove = DataStructureUtils.difference(state.getVariables(), vars);
		return state.removeVariables(varsToRemove);
	}
}
