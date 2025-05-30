package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceUtils<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	public InterferenceUtils() {
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<String> getThreadsThatCanInterfere(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		if (result.getStates().isEmpty()) {
			return Collections.emptySet();
		}
		final Set<String> threadNameSet = result.getStates().iterator().next().threadCounter().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = GuardedStateTransformer.getThreadInstanceStateUnion(result).getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread) {
				possibleInterferenceSet.add(threadName);
			}
		}
		return possibleInterferenceSet;
	}

	public Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> createValidInterferenceThreadPairs(
			final String ownerThread, final AbstractInterferenceState<STATE, ACTION, LOC> interferences2,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result) {
		final Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

//		final var interferingThreads = getThreadsThatCanInterfere(result, ownerThread);
		final var interferingThreads = result.getStates().iterator().next().threadCounter().getThreadNameSet();
		for (final String interferenceThreadName : interferingThreads) {
			final var interferences = interferences2.getInterferencesForThread(interferenceThreadName);
			if (interferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : interferences) {
				if (interference.disjState() == null) {
					continue;
				}
				// We can remove interferences where our targetstate sourcethread is not active from the beginning,
				// no amount of other interferences applied to the state will enable this interference to be valid
				if (GuardedStateTransformer.getThreadInstanceStateUnion(interference.disjState()).getThreadInstances()
						.get(ownerThread) == 0) {
					continue;
				}
				allInterferences.add(new InterferenceWithSourceThread<>(interference, interferenceThreadName));

			}
		}
		return allInterferences;
	}

	public Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> createValidInterferenceThreadPairs(
			final String ownerThread, final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> state) {
		final Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

		final var interferingThreads = state.threadCounter().getThreadNameSet();
		for (final String interferenceThreadName : interferingThreads) {
			final var oneThreadsInterferences = interferences.getInterferencesForThread(interferenceThreadName);
			if (oneThreadsInterferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : oneThreadsInterferences) {
				if (interference.disjState() == null) {
					continue;
				}
				// We can remove interferences where our targetstate sourcethread is not active from the beginning,
				// no amount of other interferences applied to the state will enable this interference to be valid
				if (GuardedStateTransformer.getThreadInstanceStateUnion(interference.disjState()).getThreadInstances()
						.get(ownerThread) == 0) {
					continue;
				}
				allInterferences.add(new InterferenceWithSourceThread<>(interference, interferenceThreadName));

			}
		}
		return allInterferences;
	}

	public boolean stateIsInterferableBy(final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState,
			final String ownerThread, final String interferenceThreadName,
			final Interference<STATE, ACTION, LOC> interference, final AbstractLocationMap<LOC> abstractLocationMap) {
		if (!interferingThreadIsActiveInState(ownerThread, interferenceThreadName, singleState)) {
			return false;
		}
		if (GuardedStateTransformer.getThreadInstanceStateUnion(interference.disjState()).getThreadInstances()
				.get(interferenceThreadName) > 1) {
			return true;
		}
		final Set<Integer> possibleInterferingThreadLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		final int actualInterferenceThreadLocation = abstractLocationMap
				.getAbstractLocation(interference.action().getSource());
		if ((!possibleInterferingThreadLocations.contains(actualInterferenceThreadLocation))) {
			return false;
		}
		return true;
	}

	private boolean interferingThreadIsActiveInState(final String ownerThread, final String interferenceThreadName,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {
		final var interferingThreadCount = singleState.threadCounter().getThreadInstances().get(interferenceThreadName);
		// unforked threads cant interfere
		if (interferingThreadCount < 1) {
			return false;
		}
		// self interference only when more than 1 threadinstance active
		if (interferingThreadCount < 2 && ownerThread.equals(interferenceThreadName)) {
			return false;
		}
		return true;
	}

}
