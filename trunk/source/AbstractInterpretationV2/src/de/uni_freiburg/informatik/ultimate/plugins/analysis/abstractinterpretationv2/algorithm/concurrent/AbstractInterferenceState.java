package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

record Interference<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
		ACTION action, STATE state, ThreadInstanceCounter threadcounter) {
	boolean isEqualTo(final Interference<STATE, ACTION, LOC> other) {
		return state().isEqualTo(other.state()) && threadcounter().isEqualTo(other.threadcounter());
	}
}

public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final GuardedInterferenceDomain<STATE, ACTION, LOC> mDomain;
	private final Map<String, Map<ACTION, Interference<STATE, ACTION, LOC>>> mInterferenceMap;
	private boolean mWiden = false;

	public AbstractInterferenceState(final Set<String> threadNames,
			final GuardedInterferenceDomain<STATE, ACTION, LOC> domain) {
		mInterferenceMap = new HashMap<>();
		threadNames.forEach(t -> mInterferenceMap.put(t, new HashMap<>()));
		mDomain = domain;
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION, LOC> other) {
		mInterferenceMap = new HashMap<>();
		other.mInterferenceMap.forEach((thread, map) -> {
			final var copy = new HashMap<ACTION, Interference<STATE, ACTION, LOC>>();
			map.forEach(copy::put);
			mInterferenceMap.put(thread, copy);
		});
		mDomain = other.mDomain;
	}

	public GuardedInterferenceDomain<STATE, ACTION, LOC> getDomain() {
		return mDomain;
	}

	public void setWidening() {
		mWiden = true;
	}

	public Set<Interference<STATE, ACTION, LOC>> getInterferencesForThread(final String threadName) {
		final var inner = mInterferenceMap.get(threadName);
		return inner == null ? Set.of() : new HashSet<>(inner.values());
	}

	public void addInterference(final Interference<STATE, ACTION, LOC> itf) {
		addInterference(itf.action().getSource().getProcedure(), itf.action(), itf.state(), itf.threadcounter());
	}

	public void addInterference(final String threadName, final ACTION action, final STATE state,
			final ThreadInstanceCounter counter) {
		final var threadMap = mInterferenceMap.computeIfAbsent(threadName, k -> new HashMap<>());
		final var existing = threadMap.get(action);
		Interference<STATE, ACTION, LOC> newItf;
		if (existing != null) {
			if (!mWiden) {
				newItf = new Interference<>(action, state.union(existing.state()), new ThreadInstanceCounter(counter));
			} else {
				newItf = new Interference<>(action,
						mDomain.getUnderlyingDomain().getWideningOperator().apply(state, existing.state()),
						new ThreadInstanceCounter(counter));
			}
		} else {
			newItf = new Interference<>(action, state, new ThreadInstanceCounter(counter));
		}
		threadMap.put(action, newItf);
	}

	public void clear() {
		mInterferenceMap.clear();
	}

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION, LOC> other) {
		for (final var pair : mInterferenceMap.entrySet()) {
			final var otherThreadMap = other.mInterferenceMap.get(pair.getKey());
			if (otherThreadMap == null) {
				return false;
			}
			for (final var actionItfPair : pair.getValue().entrySet()) {
				final var otherItf = otherThreadMap.get(actionItfPair.getKey());
				if (otherItf == null) {
					return false;
				}
				if (actionItfPair.getValue().state().isSubsetOf(otherItf.state()) == SubsetResult.NONE) {
					return false;
				}
			}
		}
		return true;
	}

	public Set<String> interferenceStrings() {
		return mInterferenceMap.entrySet().stream()
				.flatMap(e -> e.getValue().values().stream().map(i -> "Thread " + e.getKey() + ": " + i))
				.collect(Collectors.toSet());
	}
}
