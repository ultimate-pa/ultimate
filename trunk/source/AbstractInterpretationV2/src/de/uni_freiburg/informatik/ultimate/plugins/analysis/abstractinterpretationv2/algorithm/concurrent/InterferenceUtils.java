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
			final DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> result) {
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

	public boolean stateIsInterferableBy(final InterferenceDomainState<STATE, ACTION, LOC> singleState,
			final String ownerThread, final String interferenceThreadName,
			final Interference<STATE, ACTION, LOC> interference,
			final StaticAbstractLocationMap<LOC> abstractLocationMap) {
		// Is thread of interference even active/forked
		if (!interferingThreadIsActiveInState(ownerThread, interferenceThreadName, singleState)) {
			return false;
		}
		/*
		 * Check if interference comes from location which the interfered state thinks the interfering thread could be
		 * in. If not, it cannot be interfered by it.
		 */
		final int actualInterferenceThreadLocation = abstractLocationMap
				.getAbstractLocation(interference.action().getSource());
		final Set<Integer> possibleInterferingThreadLocations = singleState.abstractLocationState().getTracker()
				.getLocationForThread(interferenceThreadName);
		if ((!possibleInterferingThreadLocations.contains(actualInterferenceThreadLocation))) {
			return false;
		}
		return true;
	}

	private boolean interferingThreadIsActiveInState(final String ownerThread, final String interferenceThreadName,
			final InterferenceDomainState<STATE, ACTION, LOC> singleState) {
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
