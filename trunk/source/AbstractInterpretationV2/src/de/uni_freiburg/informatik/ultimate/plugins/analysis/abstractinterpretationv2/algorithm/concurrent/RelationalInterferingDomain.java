package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;

/**
 * Wrapper for an {@code IAbstractDomain} with a different post-operator to consider interferences, just like
 * {@code InterferingDomain}. Underlying domain is SIFA domain. Domain also inlcudes Threadinformation.
 */
public class RelationalInterferingDomain<STATE extends IAbstractState<STATE>, ACTION>
		implements IAbstractDomain<RelationalInterferingState<STATE, ACTION>, ACTION> {
	private final IAbstractDomain<STATE, ACTION> mUnderlyingDomain;
	private final IAbstractPostOperator<RelationalInterferingState<STATE, ACTION>, ACTION> mRelationalInterferingPostOperator;
	private final IAbstractStateBinaryOperator<RelationalInterferingState<STATE, ACTION>> mWideningOperator;
	private final ThreadInstanceCounterFactory mThreadInstanceCounterFactory;

	private final AbstractInterferenceState<STATE, ACTION> mInterferences;

	public RelationalInterferingDomain(final IIcfg<?> cfg, final IAbstractDomain<STATE, ACTION> underlying,
			final ILogger logger) {
		mThreadInstanceCounterFactory = new ThreadInstanceCounterFactory(cfg);
		mInterferences = new AbstractInterferenceState<>(cfg.getCfgSmtToolkit().getProcedures());

		mUnderlyingDomain = underlying;
		mRelationalInterferingPostOperator = new RelationalInterferingPostOperator<>(cfg, logger, mUnderlyingDomain,
				mUnderlyingDomain.getPostOperator(), this, mInterferences);
		mWideningOperator = new RelationalInterferingWideningOperator<>(underlying, mThreadInstanceCounterFactory);
	}

	public IAbstractDomain<STATE, ACTION> getUnderlyingDomain() {
		return mUnderlyingDomain;
	}

	public ThreadInstanceCounterFactory threadInstanceCounterFactory() {
		return mThreadInstanceCounterFactory;
	}

	public AbstractInterferenceState<STATE, ACTION> interferenceState() {
		return mInterferences;
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> createTopState() {
		return new RelationalInterferingState<>(mUnderlyingDomain, mUnderlyingDomain.createTopState(),
				mThreadInstanceCounterFactory.createTopState());
	}

	@Override
	public RelationalInterferingState<STATE, ACTION> createBottomState() {
		return new RelationalInterferingState<>(mUnderlyingDomain, mUnderlyingDomain.createBottomState(),
				mThreadInstanceCounterFactory.createBottomState());
	}

	public RelationalInterferingState<STATE, ACTION> createBottomPreconditionState() {
		return new RelationalInterferingState<>(mUnderlyingDomain, mUnderlyingDomain.createTopState(),
				mThreadInstanceCounterFactory.createBottomState());
	}

	@Override
	public IAbstractStateBinaryOperator<RelationalInterferingState<STATE, ACTION>> getWideningOperator() {
		return mWideningOperator;
	}

	@Override
	public IAbstractPostOperator<RelationalInterferingState<STATE, ACTION>, ACTION> getPostOperator() {
		return mRelationalInterferingPostOperator;
	}

	@Override
	public String domainDescription() {
		return "SIFA - " + mUnderlyingDomain.toString() + " with interferences";
	}
}
