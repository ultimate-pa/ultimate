package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.transformula.nonrelational.interval;

import java.util.function.Supplier;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractDomain;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractPostOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractStateBinaryOperator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.generic.LiteralCollection;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalDomainState;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalLiteralWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.domain.nonrelational.interval.IntervalSimpleWideningOperator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.preferences.AbsIntPrefInitializer;

public class IntervalDomain implements IAbstractDomain<IntervalDomainState, IcfgEdge> {

	private final ILogger mLogger;
	private final IUltimateServiceProvider mServices;
	private IAbstractStateBinaryOperator<IntervalDomainState> mWideningOperator;
	private final LiteralCollection mLiteralCollection;
	private IAbstractPostOperator<IntervalDomainState, IcfgEdge> mPostOperator;

	public IntervalDomain(final ILogger logger, final LiteralCollection literalCollection,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mLiteralCollection = literalCollection;
		mServices = services;
	}

	@Override
	public IntervalDomainState createTopState() {
		return new IntervalDomainState(mLogger, false);
	}

	@Override
	public IntervalDomainState createBottomState() {
		return new IntervalDomainState(mLogger, true);
	}

	@Override
	public IAbstractStateBinaryOperator<IntervalDomainState> getWideningOperator() {
		if (mWideningOperator == null) {
			final IPreferenceProvider ups = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final String wideningOperator = ups.getString(IntervalDomainPreferences.LABEL_INTERVAL_WIDENING_OPERATOR);

			if (wideningOperator.equals(IntervalDomainPreferences.VALUE_WIDENING_OPERATOR_SIMPLE)) {
				mWideningOperator = new IntervalSimpleWideningOperator();
			} else if (wideningOperator.equals(IntervalDomainPreferences.VALUE_WIDENING_OPERATOR_LITERALS)) {
				final IAbstractStateBinaryOperator<IntervalDomainState> rtr =
						new IntervalLiteralWideningOperator(mLiteralCollection);
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
	public IAbstractPostOperator<IntervalDomainState, IcfgEdge> getPostOperator() {
		if (mPostOperator == null) {
			final IPreferenceProvider prefs = mServices.getPreferenceProvider(Activator.PLUGIN_ID);
			final int maxParallelStates = prefs.getInt(AbsIntPrefInitializer.LABEL_MAX_PARALLEL_STATES);
			final Supplier<IntervalDomainState> topStateSupplier = this::createTopState;
			final Supplier<IntervalDomainState> bottomStateSupplier = this::createBottomState;
			mPostOperator = new IntervalPostOperator(mLogger, maxParallelStates, topStateSupplier, bottomStateSupplier);
		}
		return mPostOperator;
	}
}
