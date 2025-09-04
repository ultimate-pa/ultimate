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
public class InterferenceDomain<STATE extends IAbstractState<STATE>, ACTION extends IIcfgTransition<LOC>, LOC extends IcfgLocation>
		implements IAbstractDomain<InterferenceDomainState<STATE, ACTION, LOC>, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<InterferenceDomainState<STATE, ACTION, LOC>, ACTION> mGuardedInterferenceDomainPostOperator;
	private final IAbstractStateBinaryOperator<InterferenceDomainState<STATE, ACTION, LOC>> mWideningOperator;
	private final ThreadInstanceCounterFactory<LOC> mThreadInstanceCounterFactory;

	private final StaticAbstractLocationMap<LOC> mAbstractLocationMap;

	public static int postoperatorCalls;
	public static int postOpCacheHits;
	public static int applierCacheHits;
	public static int totalInnerInterferenceIterations;
	public static int maxStatesInOneItf;

	public InterferenceDomain(final IIcfg<? extends LOC> cfg, final IAbstractDomain<STATE, ACTION> underlying,
			final ILogger logger, final StaticAbstractLocationMap<LOC> locationMap, final int maxSize, final int maxItf,
			final AbstractInterferenceState<STATE, ACTION, LOC> interferences,
			final InterferenceCache<STATE, ACTION, LOC> cache) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory<>(cfg);
		mAbstractLocationMap = locationMap;
		mUnderlyingDomain = underlying;
		mGuardedInterferenceDomainPostOperator = new InterferenceDomainPostOperator<>(cfg, logger,
				mUnderlyingDomain.getPostOperator(), this, mAbstractLocationMap, maxItf, maxSize, interferences, cache);
		mWideningOperator = new InterferenceDomainWideningOperator<>(underlying);
		postoperatorCalls = 0;
		totalInnerInterferenceIterations = 0;
		maxStatesInOneItf = 0;
		postOpCacheHits = 0;
		applierCacheHits = 0;
	}

	public StaticAbstractLocationMap<LOC> getAbstractLocationMap() {
		return mAbstractLocationMap;
	}

	@Override
	public InterferenceDomainState<STATE, ACTION, LOC> createTopState() {
		final InterferenceDomainState<STATE, ACTION, LOC> topstate = new InterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createTopState(), null);
		return topstate;
	}

	@Override
	public InterferenceDomainState<STATE, ACTION, LOC> createBottomState() {
		final InterferenceDomainState<STATE, ACTION, LOC> topstate = new InterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createBottomState(), null);
		return topstate;
	}

	public InterferenceDomainState<STATE, ACTION, LOC> createBottomPreconditionState() {
		// the "bottomstate" of the main thread first entry location. the state is top
		final InterferenceDomainState<STATE, ACTION, LOC> bottomState = new InterferenceDomainState<>(
				mUnderlyingDomain.createTopState(), mThreadInstanceCounterFactory.createBottomState(), null);
		return bottomState;
	}

	@Override
	public IAbstractStateBinaryOperator<InterferenceDomainState<STATE, ACTION, LOC>> getWideningOperator() {
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<InterferenceDomainState<STATE, ACTION, LOC>, ACTION> getPostOperator() {
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
