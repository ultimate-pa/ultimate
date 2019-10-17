package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collection;
import java.util.Collections;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.RefinementEngineStatisticsGenerator.RefinementEngineStatisticsDefinitions;

public class IpTcStrategyModuleMCR<T extends IInterpolatingTraceCheck<LETTER>, LETTER extends IIcfgTransition<?>>
		implements IIpTcStrategyModule<MCR<LETTER>, LETTER> {

	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final IIpTcStrategyModule<T, LETTER> mIpTcModule;

	private MCR<LETTER> mMCR;

	public IpTcStrategyModuleMCR(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IIpTcStrategyModule<T, LETTER> nestedModule) {
		mPrefs = prefs;
		mIpTcModule = nestedModule;
		mLogger = logger;
	}

	@Override
	public LBool isCorrect() {
		return mIpTcModule.isCorrect();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mIpTcModule.providesRcfgProgramExecution();
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		return mIpTcModule.getRcfgProgramExecution();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return mIpTcModule.getTraceCheckReasonUnknown();
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		return mIpTcModule.getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mIpTcModule.getPredicateUnifier();
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		mIpTcModule.aggregateStatistics(stats);
		stats.addStatistics(RefinementEngineStatisticsDefinitions.INTERPOLANT_CONSOLIDATION,
				getOrConstruct().getStatistics());
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		return getOrConstruct().getInterpolantComputationStatus();
	}

	@Override
	public Collection<QualifiedTracePredicates> getPerfectInterpolantSequences() {
		final MCR<LETTER> tc = getOrConstruct();
		if (tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), true));
		}
		return Collections.emptyList();
	}

	@Override
	public Collection<QualifiedTracePredicates> getImperfectInterpolantSequences() {
		final MCR<LETTER> tc = getOrConstruct();
		if (!tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), false));
		}
		return Collections.emptyList();
	}

	@Override
	public MCR<LETTER> getOrConstruct() {
		if (mMCR == null) {
			// TODO: Where to get a trace check factory?
			mMCR = new MCR<>(mLogger, mPrefs, getPredicateUnifier(), mIpTcModule.getOrConstruct().getTrace(), null);
		}
		return mMCR;
	}
}
