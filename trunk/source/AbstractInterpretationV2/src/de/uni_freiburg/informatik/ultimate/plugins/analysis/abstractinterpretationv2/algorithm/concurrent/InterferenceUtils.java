package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent.SimpleInterferenceApplier.InterferenceWithParentThread;

public class InterferenceUtils {

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<String> getThreadsThatCanInterfere(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result,
			final String ownerThread) {
		if (result.getStates().isEmpty()) {
			return Collections.emptySet();
		}
		final Set<String> threadNameSet = result.getStates().iterator().next().threadCounter().getThreadNameSet();
		final Set<String> possibleInterferenceSet = new HashSet<>();
		final var procedureMap = GuardedStateTransformer.getThreadInstanceState(result).getThreadInstances();
		for (final String threadName : threadNameSet) {
			final int threadInstances = procedureMap.get(threadName);
			if (threadInstances >= 2 || threadName != ownerThread) {
				possibleInterferenceSet.add(threadName);
			}
		}
		return possibleInterferenceSet;
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<InterferenceWithParentThread<STATE, ACTION, LOC>> getValidInterferences(
			final Set<String> interferingThreads, final String ownerThread,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences2,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result) {
		final Set<de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent.SimpleInterferenceApplier.InterferenceWithParentThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

		for (final String interferenceThreadName : interferingThreads) {
			// TODO: possibly exclude states from disjunction where interferingthread is not active
			if (GuardedStateTransformer.getThreadInstanceState(result).getThreadInstances()
					.get(interferenceThreadName) == 0) {
				continue;
			}
			final var interferences = interferences2.getInterferencesForThread(interferenceThreadName);
			if (interferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : interferences) {
				if (interference.disjState() == null) {
					continue;
				}
				if (GuardedStateTransformer.getThreadInstanceState(interference.disjState()).getThreadInstances()
						.get(ownerThread) == 0) {
					continue;
				}
				allInterferences.add(new InterferenceWithParentThread<>(interference, interferenceThreadName));

			}
		}
		return allInterferences;
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> boolean matchesLocation(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState, final String ownerThread,
			final String interferenceThreadName, final Interference<STATE, ACTION, LOC> interference,
			final AbstractLocationMap<LOC> mAbstractLocationMap) {
		final var itfThinksStateIs = GuardedStateTransformer.getAbstractLocationUnion(interference.disjState())
				.getTracker().getLocationForThread(ownerThread);
		final var realLoc = singleState.abstractLocationState().getintLoc();
		if (!itfThinksStateIs.contains(realLoc)) {
			return false;
		}
		if (singleState.threadCounter().getThreadInstances().get(interferenceThreadName) < 1) {
			return false;
		}
		if (GuardedStateTransformer.getThreadInstanceState(interference.disjState()).getThreadInstances()
				.get(ownerThread) == 0) {
			return false;
		}
		final Set<Integer> possibleInterferingLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		final int interferenceLocation = mAbstractLocationMap.getAbstractLocation(interference.action().getSource());
		if ((!possibleInterferingLocations.contains(interferenceLocation)
				|| !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 0))
				&& !(ownerThread.equals(interferenceThreadName))
				&& !(singleState.threadCounter().getThreadInstances().get(interferenceThreadName) > 1)) {
			return false;
		}
		return true;
	}

}
