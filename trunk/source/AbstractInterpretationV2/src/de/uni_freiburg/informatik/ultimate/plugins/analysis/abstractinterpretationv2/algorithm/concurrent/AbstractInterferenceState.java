package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

record Interference<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>(
		ACTION action, STATE state, ThreadInstanceCounter threadcounter) {
}

// TODO: we assume that an action has a unique hash, throughout all threads (and within one).
// if this is untrue, this is unsound. Then somehow get unique location from ACTION if possible when
// adding interferences
public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private Map<String, Set<Interference<STATE, ACTION, LOC>>> mThreadInterferenceMap;
	private final Map<ACTION, Set<Interference<STATE, ACTION, LOC>>> mIdentifyMap;

	public AbstractInterferenceState(final Set<String> threadNames) {
		mIdentifyMap = new HashMap<>();
		mThreadInterferenceMap = new HashMap<>();
		threadNames.stream().forEach(t -> mThreadInterferenceMap.put(t, new HashSet<>()));
	}

	public AbstractInterferenceState(final AbstractInterferenceState<STATE, ACTION, LOC> other) {
		mIdentifyMap = new HashMap<>(other.getIdentifyMap());
		mThreadInterferenceMap = new HashMap<>();
		other.getInterferenceMapHashRelation().keySet().stream().forEach(
				t -> mThreadInterferenceMap.put(t, new HashSet<>(other.getInterferenceMapHashRelation().get(t))));
	}

	public Map<ACTION, Set<Interference<STATE, ACTION, LOC>>> getIdentifyMap() {
		return mIdentifyMap;
	}

	public void changeInterferences(final Map<String, Set<Interference<STATE, ACTION, LOC>>> newMap) {
		mThreadInterferenceMap = newMap;
	}

	public Set<Interference<STATE, ACTION, LOC>> getInterferencesForThread(final String threadName) {
		return mThreadInterferenceMap.get(threadName);
	}

	public void addInterference(final Interference<STATE, ACTION, LOC> itf) {
		addInterference(itf.action().getSource().getProcedure(), itf.action(), itf.state(), itf.threadcounter());
	}

	public void addInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		if (mIdentifyMap.get(transition) == null) {
			mIdentifyMap.put(transition, new HashSet<>());
		}
		final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
		mIdentifyMap.get(transition).add(interference);
		mThreadInterferenceMap.get(threadName).add(interference);
	}

	public void addForkInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		if (mIdentifyMap.get(transition) == null) {
			mIdentifyMap.put(transition, new HashSet<>());
		}
		final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
		mIdentifyMap.get(transition).add(interference);
		mThreadInterferenceMap.get(threadName).add(interference);
	}

	public Map<String, Set<Interference<STATE, ACTION, LOC>>> getInterferenceMapHashRelation() {
		return mThreadInterferenceMap;
	}

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION, LOC> other) {
		for (final Map.Entry<ACTION, Set<Interference<STATE, ACTION, LOC>>> entry : mIdentifyMap.entrySet()) {
			final ACTION action = entry.getKey();
			final Set<Interference<STATE, ACTION, LOC>> thisSet = entry.getValue();
			final Set<Interference<STATE, ACTION, LOC>> otherSet = other.getIdentifyMap().get(action);
			if (otherSet == null) {
				return false;
			}
			outer: for (final Interference<STATE, ACTION, LOC> thisInt : thisSet) {

				for (final Interference<STATE, ACTION, LOC> otherInt : otherSet) {
					if (thisInt.state().isSubsetOf(otherInt.state()) != SubsetResult.NONE) {
						continue outer;
					}
				}
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

	public AbstractInterferenceState<STATE, ACTION, LOC> union(
			final AbstractInterferenceState<STATE, ACTION, LOC> other) {

		final Set<String> unionThreads = new HashSet<>(mThreadInterferenceMap.keySet());
		unionThreads.addAll(other.mThreadInterferenceMap.keySet());
		final AbstractInterferenceState<STATE, ACTION, LOC> result = new AbstractInterferenceState<>(unionThreads);

		final Map<ACTION, Set<Interference<STATE, ACTION, LOC>>> mergedMap = Stream
				.concat(mIdentifyMap.entrySet().stream(), other.mIdentifyMap.entrySet().stream())
				.collect(Collectors.toMap(Map.Entry::getKey, e -> new HashSet<>(e.getValue()), (set1, set2) -> {
					set1.addAll(set2);
					return set1;
				}));

		for (final Map.Entry<ACTION, Set<Interference<STATE, ACTION, LOC>>> entry : mergedMap.entrySet()) {
			for (final Interference<STATE, ACTION, LOC> interference : entry.getValue()) {
				result.addInterference(interference);
			}
		}

		return result;
	}
}
