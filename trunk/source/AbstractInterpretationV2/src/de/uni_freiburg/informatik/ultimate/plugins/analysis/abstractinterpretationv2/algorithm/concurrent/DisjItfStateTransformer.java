package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public final class DisjItfStateTransformer {

	public DisjItfStateTransformer() {
		throw new AssertionError("Should not instantiate this class, call the statiic methods");
	}

	private static <S> Set<S> mapStates(final Set<S> states, final Function<S, S> transformer) {
		return states.stream().map(transformer).collect(Collectors.toSet());
	}

	public static <STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation> DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> assignForkId(
			final String threadName, final int forkId, final LOC forkLoc, final boolean inLoop,
			final DisjunctiveAbstractState<InterferenceDomainState<STATE, ACTION, LOC>> disj) {
		final Set<InterferenceDomainState<STATE, ACTION, LOC>> states = disj.getStates();
		return DisjunctiveAbstractState
				.createDisjunction(mapStates(states, s -> s.assignForkId(threadName, forkId, forkLoc, inLoop)));
	}
}
