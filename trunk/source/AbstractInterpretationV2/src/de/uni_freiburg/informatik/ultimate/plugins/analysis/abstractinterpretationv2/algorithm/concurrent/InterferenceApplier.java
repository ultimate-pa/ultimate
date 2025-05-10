package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;
import java.util.stream.Collectors;

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
			final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> postOp,
			final int maxSize) {

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
		final var filtered = DisjunctiveAbstractState.createDisjunction(intersectionState.getStates().stream()
				.filter(s -> s != null && s.threadCounter() != null && s.abstractLocationState() != null)
				.collect(Collectors.toSet()), maxSize);

		if (filtered.getStates().size() == 0 || filtered.isBottom()) {
			return null;
		}
		// postop
		final var realLocation = GuardedStateTransformer.getAbstractLocationUnion(disjunctiveAbstractState).getLoc();
		final var postStateBroken = filtered.apply(postOp, action);
		// SET TO ORIGINAL LOCATION (apply moves the state as if it is now the location of target state of itf trans
		var postState = GuardedStateTransformer.copyToNewStateLocation(realLocation, postStateBroken);
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

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToSTATEsingle(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disjunctiveAbstractState,
			final ACTION action,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> statesThatCanBeInterferedbyItf,
			final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> postOp) {

		// Add variables to both states to be able to intersect
		var interferingState = GuardedStateTransformer.getSingleState(disjunctiveAbstractState);
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
		if (intersectionState == null || intersectionState.isBottom()) {
			return null;
		}
		// postop
		final var realLocation = interferingState.abstractLocationState().getLoc();
		final var postStateBroken = postOp.apply(intersectionState, action);
		// SET TO ORIGINAL LOCATION (apply moves the state as if it is now the location of target state of itf trans
//		final var postState = GuardedStateTransformer.copyToNewStateLocation(realLocation, postStateBroken);
		var postState = postStateBroken.stream().map(s -> s.copyToNewStateLocation(realLocation))
				.collect(Collectors.toSet());
		// TODO: sound?
		if (postState.stream().allMatch(s -> s.isEmpty()) || postState.stream().allMatch(s -> s.isBottom())) {
			return null;
		}
		// remove local variables of other state locations we used in postop
		if (!missingLocals2.isEmpty()) {
			postState = postState.stream().map(s -> s.removeVariables(missingLocals2)).collect(Collectors.toSet());
		}
		return postState;
	}
}
