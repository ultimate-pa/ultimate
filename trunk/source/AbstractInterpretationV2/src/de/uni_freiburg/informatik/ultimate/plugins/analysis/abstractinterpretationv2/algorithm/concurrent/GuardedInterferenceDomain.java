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
	private final ThreadInstanceCounterFactory<LOC> mThreadInstanceCounterFactory;

	private final AbstractLocationMap<LOC> mAbstractLocationMap;
	public boolean mWiden = false;

	public static int postoperatorCalls;
	public static int postOpCacheHits;
	public static int applierCacheHits;
	public static int totalInnerInterferenceIterations;
	public static int maxStatesInOneItf;

	public GuardedInterferenceDomain(final IIcfg<? extends LOC> cfg, final IAbstractDomain<STATE, ACTION> underlying,
			final ILogger logger, final AbstractLocationMap<LOC> locationMap, final int maxSize, final int maxItf,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final GuardedInterferenceCache<STATE, ACTION, LOC> cache) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory<>(cfg);
		mAbstractLocationMap = locationMap;
		mUnderlyingDomain = underlying;
		mGuardedInterferenceDomainPostOperator = new GuardedInterferenceDomainPostOperator<>(cfg, logger,
				mUnderlyingDomain.getPostOperator(), this, mAbstractLocationMap, maxItf, maxSize, interferences, cache);
		mWideningOperator = new GuardedStateWideningOperator<>(underlying);
		postoperatorCalls = 0;
		totalInnerInterferenceIterations = 0;
		maxStatesInOneItf = 0;
		postOpCacheHits = 0;
		applierCacheHits = 0;
	}

	public AbstractLocationMap<LOC> getAbstractLocationMap() {
		return mAbstractLocationMap;
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
