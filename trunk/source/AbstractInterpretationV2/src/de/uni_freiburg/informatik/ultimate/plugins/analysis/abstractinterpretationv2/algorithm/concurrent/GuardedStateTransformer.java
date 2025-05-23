package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public final class GuardedStateTransformer {

	public GuardedStateTransformer() {
		throw new AssertionError("Should not instantiate this class, call the statiic methods");
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> ThreadInstanceCounter getThreadInstanceStateUnion(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final ThreadInstanceCounter unionCounter = disj.getStates().stream().map(s -> s.threadCounter())
				.reduce((a, b) -> a.union(b))
				.orElseThrow(() -> new IllegalStateException("Trying to get threadinstancestate from empty list"));
		return unionCounter;
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> AbstractLocationState<LOC> getAbstractLocationUnion(
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final AbstractLocationState<LOC> unionLoc = disj.getStates().stream().map(s -> s.abstractLocationState())
				.reduce((a, b) -> a.union(b))
				.orElseThrow(() -> new IllegalStateException("Trying to get abstractlocationstate from empty list"));
		return unionLoc;
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> GuardedInterferenceDomainState<STATE, ACTION, LOC> getSingleState(
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

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> initializeLocation(
			final LOC location, final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState
				.createDisjunction(mapStates(states, s -> s.initializeLocation(location, globalMap, threadNames)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> initializeLocation(
			final LOC location, final AbstractLocationMap<LOC> globalMap, final Set<String> threadNames,
			final Set<LOC> forkLocs,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState.createDisjunction(
				mapStates(states, s -> s.initializeLocation(location, globalMap, threadNames, forkLocs)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> movedTo(
			final String threadName, final int newLocation, final LOC newLoc,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState
				.createDisjunction(mapStates(states, s -> s.movedTo(threadName, newLocation, newLoc)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> copyToNewStateLocation(
			final LOC newLoc, final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState.createDisjunction(mapStates(states, s -> s.copyToNewStateLocation(newLoc)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> setThreadsActive(
			final Collection<String> forkingStrings,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState.createDisjunction(mapStates(states, s -> s.setThreadsActive(forkingStrings)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> setThreadsInf(
			final Collection<String> forkingStrings,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState.createDisjunction(mapStates(states, s -> s.setThreadsInf(forkingStrings)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> incrementThread(
			final String thread,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState.createDisjunction(mapStates(states, s -> s.incrementThread(thread)));
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> apply(
			final IAbstractPostOperator<STATE, ACTION> underlyingPostOp, final ACTION transition,
			final DisjunctiveAbstractState<GuardedInterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<GuardedInterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		final var newStates = states.stream()
				.flatMap(s -> underlyingPostOp.apply(s.state(), transition).stream().filter(a -> !a.isBottom())
						.map(newState -> new GuardedInterferenceDomainState<STATE, ACTION, LOC>(newState,
								s.threadCounter(), s.abstractLocationState().copyToNewState(transition.getTarget()))))
				.collect(Collectors.toSet());
		return DisjunctiveAbstractState.createDisjunction(newStates);
	}
}
