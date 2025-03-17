package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;

record Interference<STATE extends IAbstractState<STATE>, ACTION>(ACTION action, STATE state,
		ThreadInstanceCounter threadcounter) {
}

// TODO: we assume that an action is unique, throughout all threads.
// if this is untrue, this is unsound. Then somehow get unique location from ACTION if possible when
// adding interferences
public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION> {
	private Map<String, Set<Interference<STATE, ACTION>>> mThreadInterferenceMap;
	private final Map<ACTION, Interference<STATE, ACTION>> mIdentifyMap;

	public AbstractInterferenceState(final Set<String> threadNames) {
		mIdentifyMap = new HashMap<>();
		mThreadInterferenceMap = new HashMap<>();
		threadNames.stream().forEach(t -> mThreadInterferenceMap.put(t, new HashSet<>()));
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION> other) {
		mIdentifyMap = new HashMap<>(other.getIdentifyMap());
		mThreadInterferenceMap = new HashMap<>();
		other.getInterferenceMapHashRelation().keySet().stream().forEach(
				t -> mThreadInterferenceMap.put(t, new HashSet<>(other.getInterferenceMapHashRelation().get(t))));
	}

	public Map<ACTION, Interference<STATE, ACTION>> getIdentifyMap() {
		return mIdentifyMap;
	}

	public void changeInterferences(final Map<String, Set<Interference<STATE, ACTION>>> newMap) {
		mThreadInterferenceMap = newMap;
	}

	public Set<Interference<STATE, ACTION>> getInterferencesForThread(final String threadName) {
		return mThreadInterferenceMap.get(threadName);
	}

	public void addInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
		mThreadInterferenceMap.get(threadName).add(interference);
		mIdentifyMap.put(interference.action(), interference);
	}

	public void addForkInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
		mThreadInterferenceMap.get(threadName).add(interference);
		mIdentifyMap.put(interference.action(), interference);
	}

	public Map<String, Set<Interference<STATE, ACTION>>> getInterferenceMapHashRelation() {
		return mThreadInterferenceMap;
	}

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION> other) {
		for (final ACTION action : mIdentifyMap.keySet()) {
			final var thisInterference = mIdentifyMap.get(action);
			final var otherInterference = other.getIdentifyMap().get(action);

			if (thisInterference == null && otherInterference == null) {
				continue;
			}
			if (thisInterference == null || otherInterference == null) {
				return false;
			}
			if (thisInterference.state().isSubsetOf(otherInterference.state()) == SubsetResult.NONE) {
				return false;
			}
		}
		return true;
	}

	public Set<String> interferenceStrings() {
		return getInterferenceMapHashRelation().keySet().stream()
				.flatMap(thread -> getInterferencesForThread(thread).stream().map(i -> "Thread " + thread + ": " + i))
				.collect(Collectors.toSet());
	}
}
