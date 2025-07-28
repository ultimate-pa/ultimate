package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceUtils<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {

	public InterferenceUtils() {
	}

	public Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> createValidInterferenceThreadPairs(
			final String ownerThread, final AbstractInterferenceState<STATE, ACTION, LOC> interferences2,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> result) {
		final Set<InterferenceWithSourceThread<STATE, ACTION, LOC>> allInterferences = new LinkedHashSet<>();

		final var interferingThreads = result.getStates().iterator().next().threadCounter().getThreadNameSet();
		for (final String interferenceThreadName : interferingThreads) {
			final var interferences = interferences2.getInterferencesForThread(interferenceThreadName);
			if (interferences == null) {
				continue;
			}
			for (final Interference<STATE, ACTION, LOC> interference : interferences) {
				if (interference.preState() == null) {
					continue;
				}
				// We can remove interferences where our targetstate sourcethread is not active from the beginning,
				// no amount of other interferences applied to the state will enable this interference to be valid
				final var interferingThreadsPerspective = interference.preState().threadCounter().getThreadInstances()
						.get(ownerThread).getUpper();
				if (interferingThreadsPerspective == null || (!interferingThreadsPerspective.isInfinity()
						&& interferingThreadsPerspective.getValue().intValue() == 0)) {
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
		// Is thread of interference even active/forked
		if (!interferingThreadIsActiveInState(ownerThread, interferenceThreadName, singleState)) {
			return false;
		}
		/*
		 * Special check for self-interference, then locations have to be handled differently. ATM we ignore locations,
		 * which is a sound, but unprecise, overapproximtation.
		 */
//		if (interference.preState().threadCounter().getThreadInstances().get(interferenceThreadName) > 1) {
//			return true;
//		}
		/*
		 * Check if interference comes from location which the interfered state thinks the interfering thread could be
		 * in. If not, it cannot be interfered by it.
		 */
		final int actualInterferenceThreadLocation = abstractLocationMap
				.getAbstractLocation(interference.action().getSource());
		if (ownerThread.equals(interferenceThreadName)) {
			final Set<Integer> selfLocation = singleState.abstractLocationState().getTracker()
					.getLocationForSelfThread(interferenceThreadName);
			if ((!selfLocation.contains(actualInterferenceThreadLocation))) {
				return false;
			}
			return true;
		}
		final Set<Integer> possibleInterferingThreadLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		if (nonMainThreadCanMove(singleState, interferenceThreadName, actualInterferenceThreadLocation)) {
			return true;
		}
		if ((!possibleInterferingThreadLocations.contains(actualInterferenceThreadLocation))) {
			return false;
		}
		return true;
	}

	private boolean nonMainThreadCanMove(final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState,
			final String interferenceThreadName, final int actualInterferenceThreadLocation) {
		final var nonMainThreadLocations = singleState.abstractLocationState().getTracker()
				.getLocationForSelfThread(interferenceThreadName);
		if (nonMainThreadLocations.contains(actualInterferenceThreadLocation)) {
			return true;
		}
		return false;
	}

	private boolean interferingThreadIsActiveInState(final String ownerThread, final String interferenceThreadName,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> singleState) {
		final var interferingThreadCount = singleState.threadCounter().getThreadInstances().get(interferenceThreadName);
		if (interferingThreadCount.getUpper().isInfinity()) {
			return true;
		}
		if (interferingThreadCount.getUpper() == null) {
			return false;
		}
		// Unforked threads cant interfere
		if (interferingThreadCount.getUpper().getValue().intValue() < 1) {
			return false;
		}
		// Self interference only when more than 1 threadinstance active
		if (interferingThreadCount.getUpper().getValue().intValue() < 2 && ownerThread.equals(interferenceThreadName)) {
			return false;
		}
		return true;
	}

}
