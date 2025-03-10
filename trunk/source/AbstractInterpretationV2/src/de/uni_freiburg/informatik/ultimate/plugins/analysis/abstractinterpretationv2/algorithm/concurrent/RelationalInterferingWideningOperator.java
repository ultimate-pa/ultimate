package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;

public class RelationalInterferingWideningOperator<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractStateBinaryOperator<RelationalInterferingState<STATE, ACTION>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;
	private final AbstractInterferenceState<STATE, ACTION> mInterferences;

	public RelationalInterferingWideningOperator(final IAbstractDomain<STATE, ACTION> underlying,
			final ThreadInstanceCounterFactory threadFactory,
			final AbstractInterferenceState<STATE, ACTION> interferences) {
		mUnderlyingDomain = underlying;
		mThreadInstanceCounterFactory = threadFactory;
		mInterferences = interferences;
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> apply(final RelationalInterferingState<STATE, ACTION> first,
			final RelationalInterferingState<STATE, ACTION> second) {
		final var widenedThreadCounter =
				mThreadInstanceCounterFactory.widen(first.getThreadInstanceState(), second.getThreadInstanceState());
		return new RelationalInterferingState<>(mUnderlyingDomain,
				mUnderlyingDomain.getWideningOperator().apply(first.getStateCopy(), second.getStateCopy()),
				widenedThreadCounter, mInterferences);
	}
}
