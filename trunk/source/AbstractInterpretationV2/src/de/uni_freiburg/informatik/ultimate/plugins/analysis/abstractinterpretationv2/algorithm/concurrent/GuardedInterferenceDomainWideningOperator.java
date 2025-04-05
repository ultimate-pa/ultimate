package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

public class GuardedInterferenceDomainWideningOperator<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractStateBinaryOperator<GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC>> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	public GuardedInterferenceDomainWideningOperator(final IAbstractDomain<STATE, ACTION> underlying,
			final ThreadInstanceCounterFactory threadFactory) {
		mUnderlyingDomain = underlying;
		mThreadInstanceCounterFactory = threadFactory;
	}

	@Override
	public GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> apply(
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> first,
			final GuardedInterferenceDomainStateDisj<STATE, ACTION, LOC> second) {
		final Set<SingleStateRecord<STATE, LOC>> newStates = new HashSet<>();
		for (final SingleStateRecord<STATE, LOC> s1 : first.getStates()) {
			for (final SingleStateRecord<STATE, LOC> s2 : second.getStates()) {
				final STATE widenedUnderlying = mUnderlyingDomain.getWideningOperator().apply(s1.state(), s2.state());
				final ThreadInstanceCounter widenedTC = mThreadInstanceCounterFactory.widen(s1.threadCounter(),
						s2.threadCounter());
				// TODO: join fine for abstractlocation widening?
				final AbstractLocationState<LOC> joinedLoc = s1.abstractLocationState()
						.union(s2.abstractLocationState());
				newStates.add(new SingleStateRecord<>(widenedUnderlying, widenedTC, joinedLoc));
			}
		}
		return new GuardedInterferenceDomainStateDisj<>(mUnderlyingDomain, 999, newStates);
	}
}
