package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class GuardedInterferenceDomainStateFactory<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> {
	private final IAbstractDomain<STATE, ACTION> mUnderlying;

	public GuardedInterferenceDomainStateFactory(final IAbstractDomain<STATE, ACTION> underlying) {
		mUnderlying = underlying;
	}

	public IAbstractDomain<STATE, ACTION> underlyingDomain() {
		return mUnderlying;
	}

	public ThreadInstanceCounter getThreadInstanceState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final var singleState = getSingleState(disj);
		return singleState.threadCounter();
	}

	/**
	 * Pointwise join of states, including pointwise threadcounter and abstractlocation joins
	 */
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> getSingleState(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final var states = disj.getStates();
		if (states.isEmpty()) {
			return null;
		}
		final var it = states.iterator();
		GuardedInterferenceDomainState<STATE, ACTION, LOC> merged = it.next();

		while (it.hasNext()) {
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> next = it.next();
			final STATE mergedState = merged.state().union(next.state());
			final ThreadInstanceCounter mergedThreads = merged.threadCounter().union(next.threadCounter());
			final AbstractLocationState<LOC> mergedLocation = merged.abstractLocationState()
					.union(next.abstractLocationState());
			merged = new GuardedInterferenceDomainState<>(mergedState, mergedThreads, mergedLocation);
		}
		return merged;
	}

	private static <S> Set<S> mapStates(final Set<S> states, final Function<S, S> transformer) {
		return states.stream().map(transformer).collect(Collectors.toSet());
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.initializeLocation(location, globalMap, threadNames));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> initializeLocation(final LOC location,
			final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames, final Set<LOC> forkLocs,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.initializeLocation(location, globalMap, threadNames, forkLocs));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> movedTo(final String threadName,
			final int newLocation, final LOC newLoc,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.movedTo(threadName, newLocation, newLoc));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> setThreadsActive(
			final Collection<String> forkingStrings,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.setThreadsActive(forkingStrings));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> setThreadsInf(
			final Collection<String> forkingStrings,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.setThreadsInf(forkingStrings));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> incrementThread(final String thread,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		return mapStates(states, s -> s.incrementThread(thread));
	}

	public Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final IAbstractPostOperator<STATE, ACTION> underlyingPostOp, final ACTION transition,
			final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states) {
		final var newStates = states.stream()
				.flatMap(s -> underlyingPostOp.apply(s.state(), transition).stream().filter(a -> !a.isBottom())
						.map(newState -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(newState,
								s.threadCounter(), s.abstractLocationState().copyToNewState(transition.getTarget()))))
				.collect(Collectors.toSet());
		return newStates;
	}
}
