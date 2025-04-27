package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;

/**
 * Wrapper for an {@code IAbstractDomain} with a different post-operator to consider interferences, just like
 * {@code InterferingDomain}. Underlying domain is SIFA domain. Domain also inlcudes Threadinformation.
 */
public class GuardedInterferenceDomain<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractDomain<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> mGuardedInterferenceDomainPostOperator;
	private final IAbstractStateBinaryOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> mWideningOperator;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	int locationCounter = 0;
	public boolean mWiden = false;

	public GuardedInterferenceDomain(final IIcfg<? extends LOC> cfg, final IAbstractDomain<STATE, ACTION> underlying,
			final ILogger logger, final AbstractLocationMap<LOC> locationMap, final int maxSize, final int maxItf,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory(cfg);
		mAbstractLocationMap = locationMap;
		mUnderlyingDomain = underlying;
		mGuardedInterferenceDomainPostOperator = new GuardedInterferenceDomainPostOperator<>(cfg, logger,
				mUnderlyingDomain.getPostOperator(), this, mAbstractLocationMap, maxItf, maxSize, interferences);
		mWideningOperator = new GuardedStateWideningOperator<>(underlying);
	}

	public AbstractLocationMap<LOC> getAbstractLocationMap() {
		return mAbstractLocationMap;
	}

	public IAbstractDomain<STATE, ACTION> getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public ThreadInstanceCounterFactory threadInstanceCounterFactory() {
		return mThreadInstanceCounterFactory;
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> createTopState() {
		final GuardedInterferenceDomainState<STATE, ACTION, LOC> topstate = new GuardedInterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createTopState(), null);
		return topstate;
	}

	@Override
	public GuardedInterferenceDomainState<STATE, ACTION, LOC> createBottomState() {
		final GuardedInterferenceDomainState<STATE, ACTION, LOC> topstate = new GuardedInterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createBottomState(), null);
		return topstate;
	}

	public GuardedInterferenceDomainState<STATE, ACTION, LOC> createBottomPreconditionState() {
		// the "bottomstate" of the main thread first entry location. the state is top
		final GuardedInterferenceDomainState<STATE, ACTION, LOC> bottomState = new GuardedInterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createBottomState(), null);
		return bottomState;
	}

	@Override
	public IAbstractStateBinaryOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>> getWideningOperator() {
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<GuardedInterferenceDomainState<STATE, ACTION, LOC>, ACTION> getPostOperator() {
		return mGuardedInterferenceDomainPostOperator;
	}

	@Override
	public String domainDescription() {
		return mUnderlyingDomain.toString() + " with interferences";
	}

	@Override
	public void beforeFixpointComputation(final Object... objects) {
		mUnderlyingDomain.beforeFixpointComputation(objects);
	}

}
