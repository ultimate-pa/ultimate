package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collections;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceWideningOperator<UNDERLYINGSTATE extends IAbstractState<UNDERLYINGSTATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> mDomain;

	public InterferenceWideningOperator(final GuardedInterferenceDomain<UNDERLYINGSTATE, ACTION, LOC> domain) {
		mDomain = domain;
	}

	public AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> calcWidenedInterferences(
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> oldI,
			final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> newI) {

		final Set<String> allThreads = new HashSet<>(oldI.getInterferenceMapHashRelation().keySet());
		allThreads.addAll(newI.getInterferenceMapHashRelation().keySet());
		final Map<ACTION, Set<Interference<UNDERLYINGSTATE, ACTION, LOC>>> oldMap = oldI.getIdentifyMap();
		final Map<ACTION, Set<Interference<UNDERLYINGSTATE, ACTION, LOC>>> newMap = newI.getIdentifyMap();

		final Set<ACTION> allActions = new HashSet<>(oldMap.keySet());
		allActions.addAll(newMap.keySet());
		final AbstractInterferenceState<UNDERLYINGSTATE, ACTION, LOC> result = new AbstractInterferenceState<>(
				allThreads);
		for (final ACTION act : allActions) {

			final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> oldSet = oldMap.getOrDefault(act,
					Collections.emptySet());
			final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> newSet = newMap.getOrDefault(act,
					Collections.emptySet());
			if (oldSet.isEmpty() && newSet.isEmpty()) {
				continue;
			}
			final UNDERLYINGSTATE oldAggState = joinAllStates(oldSet);
			final UNDERLYINGSTATE newAggState = joinAllStates(newSet);

			final ThreadInstanceCounter oldAggCnt = joinAllCounters(oldSet);
			final ThreadInstanceCounter newAggCnt = joinAllCounters(newSet);

			UNDERLYINGSTATE widenedState;
			ThreadInstanceCounter widenedCnt;

			if (oldSet.isEmpty()) {
				widenedState = newAggState;
				widenedCnt = newAggCnt;

			} else if (newSet.isEmpty()) {
				widenedState = oldAggState;
				widenedCnt = oldAggCnt;

			} else {
				widenedState = combineStates(oldAggState, newAggState);
				widenedCnt = oldAggCnt.union(newAggCnt);
			}

			result.addInterference(act.getSource().getProcedure(), act, widenedState, widenedCnt);
		}

		return result;
	}

	private UNDERLYINGSTATE joinAllStates(final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> set) {
		UNDERLYINGSTATE acc = null;
		for (final Interference<UNDERLYINGSTATE, ACTION, LOC> it : set) {
			acc = (acc == null) ? it.state() : acc.union(it.state());
		}
		return acc;
	}

	private ThreadInstanceCounter joinAllCounters(final Set<Interference<UNDERLYINGSTATE, ACTION, LOC>> set) {
		ThreadInstanceCounter acc = null;
		for (final Interference<UNDERLYINGSTATE, ACTION, LOC> it : set) {
			acc = (acc == null) ? it.threadcounter() : acc.union(it.threadcounter());
		}
		return acc;
	}

	private UNDERLYINGSTATE combineStates(final UNDERLYINGSTATE state1, final UNDERLYINGSTATE state2) {
		if (state1 == null && state2 == null) {
			return null;
		}
		if (state1 == null) {
			return state2;
		}
		if (state2 == null) {
			return state1;
		}
		return mDomain.getUnderlyingDomain().getWideningOperator().apply(state1, state2);
	}

}
