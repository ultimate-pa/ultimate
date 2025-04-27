package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceApplier {

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> STATE applyInterferenceToSTATEsingle(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleInterferingState, final ACTION action,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState,
			final IAbstractPostOperator<STATE, ACTION> mUnderlyingPostOp) {

		// Add variables to both states to be able to intersect
		STATE interferingState = singleInterferingState.state();
		STATE stateState = singleState.state();
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
		final STATE intersectionState = stateState.intersect(interferingState);
		if (intersectionState.isBottom()) {
			return null;
		}
		// postop
		Collection<STATE> postState = mUnderlyingPostOp.apply(intersectionState, action);
		// TODO: sound?
		if (postState.isEmpty()) {
			return null;
		}
		if (!missingLocals2.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toList());
		}
		STATE unionState = postState.iterator().next();
		for (final STATE state : postState) {
			if (state != unionState) {
				unionState = unionState.union(state);
			}
		}
		if (unionState.isBottom()) {
			return null;
		}
		return unionState;
	}
}
