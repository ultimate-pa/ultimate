package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.interval;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalLiteralWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalMergeOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalSimpleWideningOperator;

public class IntervalDomain
		implements IAbstractDomain<IntervalDomainState<IProgramVarOrConst>, IcfgEdge, IProgramVarOrConst> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IAbstractStateBinaryOperator<IntervalDomainState<IProgramVarOrConst>> mWideningOperator;
	private final LiteralCollection mLiteralCollection;
	private IAbstractStateBinaryOperator<IntervalDomainState<IProgramVarOrConst>> mMergeOperator;
	private IAbstractPostOperator<IntervalDomainState<IProgramVarOrConst>, IcfgEdge, IProgramVarOrConst> mPostOperator;

	public IntervalDomain(final ILogger logger, final LiteralCollection literalCollection,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mLiteralCollection = literalCollection;
		mServices = services;
	}

	@Override
	public IntervalDomainState<IProgramVarOrConst> createFreshState() {
		return createTopState();
	}

	@Override
	public IntervalDomainState<IProgramVarOrConst> createTopState() {
		return new IntervalDomainState<>(mLogger, false);
	}

	@Override
	public IntervalDomainState<IProgramVarOrConst> createBottomState() {
		return new IntervalDomainState<>(mLogger, true);
	}

	@Override
	public IAbstractStateBinaryOperator<IntervalDomainState<IProgramVarOrConst>> getWideningOperator() {
		if (mWideningOperator == null) {
			final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final String wideningOperator = ups.getString(IntervalDomainPreferences.LABEL_INTERVAL_WIDENING_OPERATOR);

			if (wideningOperator.equals(IntervalDomainPreferences.VALUE_WIDENING_OPERATOR_SIMPLE)) {
				mWideningOperator = new IntervalSimpleWideningOperator<>();
			} else if (wideningOperator.equals(IntervalDomainPreferences.VALUE_WIDENING_OPERATOR_LITERALS)) {
				final IAbstractStateBinaryOperator<IntervalDomainState<IProgramVarOrConst>> rtr =
						new IntervalLiteralWideningOperator<>(mLiteralCollection);
				if (mLogger.isDebugEnabled()) {
					mLogger.debug("Using the following literals during widening: " + mLiteralCollection);
				}
				mWideningOperator = rtr;
			} else {
				throw new UnsupportedOperationException(
						"The widening operator " + wideningOperator + " is not implemented.");
			}
		}

		return mWideningOperator;
	}

	@Override
	public IAbstractStateBinaryOperator<IntervalDomainState<IProgramVarOrConst>> getMergeOperator() {
		if (mMergeOperator == null) {
			mMergeOperator = new IntervalMergeOperator<>();
		}
		return mMergeOperator;
	}

	@Override
	public IAbstractPostOperator<IntervalDomainState<IProgramVarOrConst>, IcfgEdge, IProgramVarOrConst>
			getPostOperator() {
		if (mPostOperator == null) {
			mPostOperator = new IntervalPostOperator(mLogger);
		}
		return mPostOperator;
	}
}
