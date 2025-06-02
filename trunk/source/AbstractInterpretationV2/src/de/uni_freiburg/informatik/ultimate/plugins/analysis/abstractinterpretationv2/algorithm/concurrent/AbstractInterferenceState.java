package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IInterferenceRepository<STATE, ACTION, LOC> {
	private final Map<String, Map<ACTION, Interference<STATE, ACTION, LOC>>> mInterferenceMap;

	public AbstractInterferenceState(final Set<String> threadNames) {
		mInterferenceMap = new HashMap<>();
		threadNames.forEach(t -> mInterferenceMap.put(t, new HashMap<>()));
	}

	@Override
	public Set<Interference<STATE, ACTION, LOC>> getInterferencesForThread(final String threadName) {
		final var inner = mInterferenceMap.get(threadName);
		return inner == null ? Set.of() : new HashSet<>(inner.values());
	}

	@Override
	public void addInterference(final Interference<STATE, ACTION, LOC> interference) {
		addInterference(interference.action().getSource().getProcedure(), interference.action(),
				interference.disjState());
	}

	public void addInterference(final String threadName, final ACTION action,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> state) {
		if (state == null) {
			return;
		}
		final var threadMap = mInterferenceMap.computeIfAbsent(threadName, k -> new HashMap<>());
		final var newItf = new Interference<>(action, state);
		threadMap.put(action, newItf);
	}

	public Set<String> interferenceStrings() {
		return mInterferenceMap.entrySet().stream()
				.flatMap(e -> e.getValue().values().stream()
						.map(i -> "Thread " + e.getKey() + ": " + i.action() + (i.disjState())))
				.collect(Collectors.toSet());
	}

	@Override
	public Collection<Interference<STATE, ACTION, LOC>> getAllInterferences() {
		return mInterferenceMap.values().stream().flatMap(m -> m.values().stream()).toList();
	}

	@Override
	public SubsetResult isSubsetOf(final IInterferenceRepository<STATE, ACTION, LOC> other) {
		for (final var pair : mInterferenceMap.entrySet()) {
			final var otherState = (AbstractInterferenceState<STATE, ACTION, LOC>) other;
			final var otherThreadMap = otherState.mInterferenceMap.get(pair.getKey());
			if (otherThreadMap == null) {
				return SubsetResult.NONE;
			}
			for (final var actionItfPair : pair.getValue().entrySet()) {
				final var otherItf = otherThreadMap.get(actionItfPair.getKey());
				if (otherItf == null || actionItfPair.getValue().disjState() == null) {
					return SubsetResult.NONE;
				}
				final var first = (actionItfPair.getValue().disjState());
				final var second = (otherItf.disjState());
				if (first.isSubsetOf(second) == SubsetResult.NONE) {
					return SubsetResult.NONE;
				}
			}
		}
		return SubsetResult.NON_STRICT;
	}
}
