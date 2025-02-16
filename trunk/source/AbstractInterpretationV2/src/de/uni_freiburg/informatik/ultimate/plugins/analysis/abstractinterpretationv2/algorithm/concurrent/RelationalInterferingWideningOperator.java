package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;

public class RelationalInterferingWideningOperator implements IAbstractStateBinaryOperator<RelationalInterferingState> {
	private final IDomain mSifaDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	private final RelationalInterferingStateFactoryAndPredicateHelper mStateFactory;

	public RelationalInterferingWideningOperator(final IDomain sifaDomain,
			final ThreadInstanceCounterFactory threadFactory,
			final RelationalInterferingStateFactoryAndPredicateHelper stateFactory) {
		mSifaDomain = sifaDomain;
		mThreadInstanceCounterFactory = threadFactory;
		mStateFactory = stateFactory;
	}

	@Override
	public RelationalInterferingState apply(final RelationalInterferingState first,
			final RelationalInterferingState second) {
		final var widenedPredicate = mSifaDomain.widen(first.getPredicate(), second.getPredicate());
		final var widenedThreadCounter =
				mThreadInstanceCounterFactory.widen(first.getThreadInstanceState(), second.getThreadInstanceState());
		return mStateFactory.getOrConstructState(widenedPredicate, first.getVariables(), widenedThreadCounter);
	}
}
