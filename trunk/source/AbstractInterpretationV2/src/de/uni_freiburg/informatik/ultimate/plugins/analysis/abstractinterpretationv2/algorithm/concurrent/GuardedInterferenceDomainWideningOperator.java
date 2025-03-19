package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;

public class GuardedInterferenceDomainWideningOperator<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractStateBinaryOperator<GuardedInterferenceDomainState<STATE, ACTION>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	public GuardedInterferenceDomainWideningOperator(final IAbstractDomain<STATE, ACTION> underlying,
			final ThreadInstanceCounterFactory threadFactory) {
		mUnderlyingDomain = underlying;
		mThreadInstanceCounterFactory = threadFactory;
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION> apply(
			final GuardedInterferenceDomainState<STATE, ACTION> first,
			final GuardedInterferenceDomainState<STATE, ACTION> second) {
		final var widenedThreadCounter = mThreadInstanceCounterFactory.widen(first.getThreadInstanceState(),
				second.getThreadInstanceState());
		return new GuardedInterferenceDomainState<>(mUnderlyingDomain,
				mUnderlyingDomain.getWideningOperator().apply(first.getUnderlyingState(), second.getUnderlyingState()),
				widenedThreadCounter);
	}
}
