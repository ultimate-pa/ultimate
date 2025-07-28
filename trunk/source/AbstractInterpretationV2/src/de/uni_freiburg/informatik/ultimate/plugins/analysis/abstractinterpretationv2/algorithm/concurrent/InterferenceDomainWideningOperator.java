package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class InterferenceDomainWideningOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractStateBinaryOperator<InterferenceDomainState<STATE, ACTION, LOC>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;

	public InterferenceDomainWideningOperator(final IAbstractDomain<STATE, ACTION> underlying) {
		mUnderlyingDomain = underlying;
	}

	@Override
	public InterferenceDomainState<STATE, ACTION, LOC> apply(
			final InterferenceDomainState<STATE, ACTION, LOC> first,
			final InterferenceDomainState<STATE, ACTION, LOC> second) {
		if (first.state() == null || first.state().isBottom()) {
			return second;
		}
		if (second.state() == null || second.state().isBottom()) {
			return first;
		}
		final var widenedState = mUnderlyingDomain.getWideningOperator().apply(first.state(), second.state());
		final var widenedTC = first.threadCounter().union(second.threadCounter());
		final AbstractLocationState<LOC> joinedLoc = first.abstractLocationState()
				.union(second.abstractLocationState());
		return new InterferenceDomainState<>(widenedState, widenedTC, joinedLoc);
	}
}