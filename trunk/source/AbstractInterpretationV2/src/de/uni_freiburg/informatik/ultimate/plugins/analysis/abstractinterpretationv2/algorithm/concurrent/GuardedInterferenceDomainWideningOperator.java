package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class GuardedInterferenceDomainWideningOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractStateBinaryOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final GuardedStateWideningOperator<STATE, ACTION, LOC> mSinGuardedStateWideningOperator;

	public GuardedInterferenceDomainWideningOperator(final IAbstractDomain<STATE, ACTION> underlying,
			final GuardedStateWideningOperator<STATE, ACTION, LOC> singleWideningOperator) {
		mUnderlyingDomain = underlying;
		mSinGuardedStateWideningOperator = singleWideningOperator;
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> apply(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> first,
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> second) {
		final var widened = first.getDisjunctiveAbstractState().widen(mSinGuardedStateWideningOperator,
				second.getDisjunctiveAbstractState());
		// TODO: problem : we lose maxsize value during this
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, widened, first.maxSize());
	}
}
