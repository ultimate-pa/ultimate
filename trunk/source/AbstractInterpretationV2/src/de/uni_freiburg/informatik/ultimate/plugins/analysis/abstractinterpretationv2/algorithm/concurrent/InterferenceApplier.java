package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

public class InterferenceApplier<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	public DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> applyInterferenceToDisjState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> interferingState,
			final ACTION action,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> targetState,
			final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> postOp,
			final int maxSize) {

		if (targetState.isBottom() || interferingState.isBottom()) {
			return null;
		}
		// Add local variables to both states to be able to intersect
		final var adjustedTarget = adjustStateForIntersection(targetState, interferingState, maxSize);
		final var adjustedInterferer = adjustStateForIntersection(interferingState, targetState, maxSize);

		final var intersectionState = adjustedTarget.intersect(adjustedInterferer);

		// throw out false states from intersection
		final var filtered = filterStates(intersectionState, maxSize);
		if (filtered.getStates().size() == 0 || filtered.isBottom()) {
			return null;
		}
		// postop
		var postState = filtered.apply(postOp, action);
		GuardedInterferenceDomain.postoperatorCalls++;

		// TODO: sound?
		if (postState.isEmpty() || postState.isBottom()) {
			return null;
		}
		// remove local variables of other state we added earlier
		final var missingLocals = DataStructureUtils.difference(interferingState.getVariables(),
				targetState.getVariables());
		if (!missingLocals.isEmpty()) {
			postState = postState.removeVariables(missingLocals);
		}
		return postState;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustStateForIntersection(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjustee,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> target,
			final int maxSize) {
		final var missingLocals = DataStructureUtils.difference(target.getVariables(), adjustee.getVariables());
		DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> adjusteeWithForeignLocals;
		if (!missingLocals.isEmpty()) {
			adjusteeWithForeignLocals = adjustee.addVariables(missingLocals);
		} else {
			adjusteeWithForeignLocals = adjustee;
		}
		final var filteredState = filterStates(adjusteeWithForeignLocals, maxSize);
		return filteredState;
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> filterStates(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> filterMe,
			final int maxSize) {
		return DisjunctiveAbstractState.createDisjunction(filterMe.getStates().stream().filter(
				s -> s != null && !s.isBottom() && s.threadCounter() != null && s.abstractLocationState() != null)
				.collect(Collectors.toSet()), maxSize);
	}

}
