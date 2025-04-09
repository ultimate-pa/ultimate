package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class GuardedStateWideningOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractStateBinaryOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	public GuardedStateWideningOperator(final IAbstractDomain<STATE, ACTION> underlying,
			final ThreadInstanceCounterFactory threadFactory) {
		mUnderlyingDomain = underlying;
		mThreadInstanceCounterFactory = threadFactory;
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> apply(
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> first,
			final GuardedInterferenceDomainState<STATE, ACTION, LOC> second) {
		final var widenedState = mUnderlyingDomain.getWideningOperator().apply(first.state(), second.state());
		final var widenedTC = mThreadInstanceCounterFactory.widen(first.threadCounter(), second.threadCounter());
		// TODO: join fine for abstractlocation widening?
		final AbstractLocationState<LOC> joinedLoc = first.abstractLocationState()
				.union(second.abstractLocationState());
		return new GuardedInterferenceDomainState<>(widenedState, widenedTC, joinedLoc);
	}
}