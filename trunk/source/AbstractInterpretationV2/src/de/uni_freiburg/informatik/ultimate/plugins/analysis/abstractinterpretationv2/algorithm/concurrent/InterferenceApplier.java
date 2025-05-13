package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

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
		if (stateState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		final var filteredStateState = DisjunctiveAbstractState
				.createDisjunction(stateState
						.getStates().stream().filter(s -> !(s.state().isBottom()) && s != null
								&& s.threadCounter() != null && s.abstractLocationState() != null)
						.collect(Collectors.toSet()), maxSize);
		final var filteredInterferingState = DisjunctiveAbstractState
				.createDisjunction(interferingState
						.getStates().stream().filter(s -> !(s.state().isBottom()) && s != null
								&& s.threadCounter() != null && s.abstractLocationState() != null)
						.collect(Collectors.toSet()), maxSize);
		final var intersectionState = filteredStateState.intersect(filteredInterferingState);
		final var filtered = DisjunctiveAbstractState.createDisjunction(intersectionState.getStates().stream()
				.filter(s -> s != null && s.threadCounter() != null && s.abstractLocationState() != null)
				.collect(Collectors.toSet()), maxSize);

		if (filtered.getStates().size() == 0 || filtered.isBottom()) {
			return null;
		}
		// postop
		final var realLocation = GuardedStateTransformer.getAbstractLocationUnion(disjunctiveAbstractState).getLoc();
		final var postStateBroken = filtered.apply(postOp, action);
		GuardedInterferenceDomain.postoperatorCalls++;
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

}
