package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceApplier {

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToSTATEsingle(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disjunctiveAbstractState,
			final ACTION action,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> statesThatCanBeInterferedbyItf,
			final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> postOp) {

		// Add variables to both states to be able to intersect
		var interferingState = disjunctiveAbstractState;
		var stateState = statesThatCanBeInterferedbyItf;
		final var missingLocals = DataStructureUtils.difference(stateState.getVariables(),
				interferingState.getVariables());
		final var missingLocals2 = DataStructureUtils.difference(interferingState.getVariables(),
				stateState.getVariables());
		if (stateState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			stateState = stateState.addVariables(missingLocals2);
		}
		if (!missingLocals.isEmpty()) {
			interferingState = interferingState.addVariables(missingLocals);
		}
		final var intersectionState = stateState.intersect(interferingState);
		if (intersectionState.isBottom()) {
			return null;
		}
		// postop
		var postState = intersectionState.apply(postOp, action);
		// TODO: sound?
		if (postState.isEmpty() || postState.isBottom()) {
			return null;
		}
		// remove local variables of other state locations we used in postop
		if (!missingLocals2.isEmpty()) {
			postState = postState.removeVariables(missingLocals2);
		}
		return postState;
	}
}
