package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceWideningOperator<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractStateBinaryOperator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> mWideningOperator;

	public InterferenceWideningOperator(
			final IAbstractStateBinaryOperator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> wideningOp) {
		mWideningOperator = wideningOp;
	}

	public AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> calcWidenedInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldInterferences,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newInterferences,
			final Set<String> threadNames, final int maxSize) {

		final Set<String> threads = threadNames;
		final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> result = new AbstractInterferenceState<>(threads);

		for (final String thread : threads) {
			final var oldMap = mapByAction(oldInterferences.getInterferencesForThread(thread));
			final var newMap = mapByAction(newInterferences.getInterferencesForThread(thread));

			final Set<ACTION> actions = new HashSet<>(oldMap.keySet());
			actions.addAll(newMap.keySet());

			for (final ACTION act : actions) {
				final var oldInterference = oldMap.get(act);
				final var newInterference = newMap.get(act);

				final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> widenedState;

				if (oldInterference == null) {
					widenedState = newInterference.disjState();
				} else if (newInterference == null) {
					widenedState = oldInterference.disjState();
				} else {
//					widenedState = combineStates(oldInterference.disjState(), newInterference.disjState());

					final var unionOp = new GuardedStateUnionOperator<UNDERLYINGSTATE, ACTION, LOC>();
					final var widenedStateSingle = mWideningOperator.apply(
							oldInterference.disjState().getSingleState(unionOp),
							newInterference.disjState().getSingleState(unionOp));
					widenedState = new DisjunctiveAbstractState<>(1, widenedStateSingle);
				}

				result.addInterference(thread, act, widenedState);
			}
		}
		return result;
	}

	private static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> reduceInterferencePrestate(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> preState,
			final int maxSize) {
		final var states = preState.getStates();
		if (states.size() <= 1) {
			return preState;
		}
		final List<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> toProcess = new ArrayList<>(states);
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result = new HashSet<>();
		final int startingLen = toProcess.size();
		while (!toProcess.isEmpty()) {
			GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> base = toProcess.remove(toProcess.size() - 1);
			final ListIterator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> it = toProcess
					.listIterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> candidate = it.next();
				if (base.state().isEqualTo(candidate.state())) {
					base = base.union(candidate);
					it.remove();
				}
			}
			result.add(base);
		}
		final int endLen = result.size();
		return DisjunctiveAbstractState.createDisjunction(result, maxSize);
	}

	private Map<ACTION, Interference<UNDERLYINGSTATE, ACTION, LOC>> mapByAction(
			final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> set) {
		return set.stream().collect(Collectors.toMap(Interference::action, i -> i));
	}

	private DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> combineStates(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> disjunctiveAbstractState,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> disjunctiveAbstractState2) {
		if (disjunctiveAbstractState == null) {
			return disjunctiveAbstractState2;
		}
		if (disjunctiveAbstractState2 == null) {
			return disjunctiveAbstractState;
		}
		return disjunctiveAbstractState.widen(mWideningOperator, disjunctiveAbstractState2);
	}
}
