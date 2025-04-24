package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
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
			final Set<String> threadNames) {

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
					widenedState = combineStates(oldInterference.disjState(), newInterference.disjState());
				}

				result.addInterference(thread, act, widenedState);
			}
		}
		return result;
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
