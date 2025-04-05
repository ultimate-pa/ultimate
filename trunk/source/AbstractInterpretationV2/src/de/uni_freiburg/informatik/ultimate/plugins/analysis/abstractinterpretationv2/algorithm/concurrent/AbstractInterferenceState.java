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
}

// TODO: we assume that an action has a unique hash, throughout all threads (and within one).
// if this is untrue, this is unsound. Then somehow get unique location from ACTION if possible when
// adding interferences
public class AbstractInterferenceState<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private Map<String, Set<Interference<STATE, ACTION, LOC>>> mThreadInterferenceMap;
	private final Map<ACTION, Interference<STATE, ACTION, LOC>> mIdentifyMap;

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

	public Map<ACTION, Interference<STATE, ACTION, LOC>> getIdentifyMap() {
		return mIdentifyMap;
	}

	public void changeInterferences(final Map<String, Set<Interference<STATE, ACTION, LOC>>> newMap) {
		mThreadInterferenceMap = newMap;
	}

	public Set<Interference<STATE, ACTION, LOC>> getInterferencesForThread(final String threadName) {
		return mThreadInterferenceMap.get(threadName);
	}

	public void addInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		if (mIdentifyMap.get(transition) != null) {
			final var existingInterf = mIdentifyMap.get(transition);
			final var interference = new Interference<>(transition, state.union(existingInterf.state()),
					new ThreadInstanceCounter(threadcounter.union(existingInterf.threadcounter())));
			mIdentifyMap.put(interference.action(), interference);
			mThreadInterferenceMap.get(threadName).add(interference);
		} else {
			final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
			mIdentifyMap.put(interference.action(), interference);
			mThreadInterferenceMap.get(threadName).add(interference);
		}
	}

	public void addForkInterference(final String threadName, final ACTION transition, final STATE state,
			final ThreadInstanceCounter threadcounter) {
		if (mIdentifyMap.get(transition) != null) {
			final var existingInterf = mIdentifyMap.get(transition);
			final var interference = new Interference<>(transition, state.union(existingInterf.state()),
					new ThreadInstanceCounter(threadcounter.union(existingInterf.threadcounter())));
			mIdentifyMap.put(interference.action(), interference);
			mThreadInterferenceMap.get(threadName).add(interference);
		} else {
			final var interference = new Interference<>(transition, state, new ThreadInstanceCounter(threadcounter));
			mIdentifyMap.put(interference.action(), interference);
			mThreadInterferenceMap.get(threadName).add(interference);
		}
	}

	public Map<String, Set<Interference<STATE, ACTION, LOC>>> getInterferenceMapHashRelation() {
		return mThreadInterferenceMap;
	}

	public boolean isSubsetOf(final AbstractInterferenceState<STATE, ACTION, LOC> other) {
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

	public AbstractInterferenceState<STATE, ACTION, LOC> union(
			final AbstractInterferenceState<STATE, ACTION, LOC> other) {
		final Set<String> unionThreads = new HashSet<>(mThreadInterferenceMap.keySet());
		unionThreads.addAll(other.mThreadInterferenceMap.keySet());
		final AbstractInterferenceState<STATE, ACTION, LOC> result = new AbstractInterferenceState<>(unionThreads);

		final Set<ACTION> allActions = new HashSet<>(mIdentifyMap.keySet());
		allActions.addAll(other.mIdentifyMap.keySet());

		for (final ACTION action : allActions) {
			final Interference<STATE, ACTION, LOC> itfThis = mIdentifyMap.get(action);
			final Interference<STATE, ACTION, LOC> itfOther = other.mIdentifyMap.get(action);

			Interference<STATE, ACTION, LOC> mergedInterf = null;
			if (itfThis != null && itfOther != null) {
				final STATE mergedState = itfThis.state().union(itfOther.state());
				final ThreadInstanceCounter mergedCounter = itfThis.threadcounter().union(itfOther.threadcounter());
				mergedInterf = new Interference<>(action, mergedState, mergedCounter);

			} else if (itfThis != null) {
				mergedInterf = itfThis;
			} else if (itfOther != null) {
				mergedInterf = itfOther;
			}

			if (mergedInterf != null) {
				result.addInterference(mergedInterf.action().getSource().getProcedure(), mergedInterf.action(),
						mergedInterf.state(), mergedInterf.threadcounter());
			}
		}

		return result;
	}
}
