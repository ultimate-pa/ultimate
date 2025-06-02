package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Collection;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public final class GuardedStateTransformer {

	public GuardedStateTransformer() {
		throw new AssertionError("Should not instantiate this class, call the statiic methods");
	}

	private static <S> Set<S> mapStates(final Set<S> states, final Function<S, S> transformer) {
		return states.stream().map(transformer).collect(Collectors.toSet());
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
}
