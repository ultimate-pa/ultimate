package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.ListIterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState.SubsetResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class StateReducer {

	public static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> reduceToLocations(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result2,
			final int maxSize) {
		final var states = result2.getStates();
		if (states.size() <= 1) {
			return result2;
		}
		return DisjunctiveAbstractState.createDisjunction(reduceToLocationsSet(states), maxSize);
	}

	public static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> reduceToLocationsSet(
			final LinkedHashSet<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> states) {
		final List<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> toProcess = new ArrayList<>(states);
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result = new HashSet<>();
		while (!toProcess.isEmpty()) {
			final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> base = toProcess
					.remove(toProcess.size() - 1);
			final ListIterator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> it = toProcess
					.listIterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> candidate = it.next();
				final var sameAbstractLocation = base.abstractLocationState()
						.isEqualTo(candidate.abstractLocationState());
				if (candidate.state().isSubsetOf(base.state()) != SubsetResult.NONE && sameAbstractLocation) {
					it.remove();
				}
			}
			result.add(base);
		}
		return result;
	}

	public static <UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> reduceToLocationsSet(
			final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> states) {
		final List<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> toProcess = new ArrayList<>(states);
		final Set<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> result = new HashSet<>();
		while (!toProcess.isEmpty()) {
			GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> base = toProcess.remove(toProcess.size() - 1);
			final ListIterator<GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC>> it = toProcess
					.listIterator();
			while (it.hasNext()) {
				final GuardedInterferenceDomainState<UNDERLYINGSTATE, ACTION, LOC> candidate = it.next();
				if (base.abstractLocationState().isEqualTo(candidate.abstractLocationState())) {
					base = base.union(candidate);
					it.remove();
				}
			}
			result.add(base);
		}
		return result;
	}
}
