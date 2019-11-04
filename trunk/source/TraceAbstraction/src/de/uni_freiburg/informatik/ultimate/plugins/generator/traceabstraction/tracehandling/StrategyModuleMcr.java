package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class StrategyModuleMcr<LETTER extends IIcfgTransition<?>>
		implements IIpTcStrategyModule<MCR<LETTER>, LETTER>, IIpAbStrategyModule<LETTER> {

	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final StrategyFactory<LETTER> mStrategyFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private MCR<LETTER> mMcr;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private AutomatonFreeRefinementEngine<LETTER> mRefinementEngine;

	public StrategyModuleMcr(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IPredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final StrategyFactory<LETTER> strategyFactory) {
		mPrefs = prefs;
		mStrategyFactory = strategyFactory;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mEmptyStackFactory = emptyStackFactory;

		// TODO: Add parameters
		final IRefinementStrategy<LETTER> initialStrategy = null;
		// final IRefinementStrategy<LETTER> initialStrategy = mStrategyFactory.constructStrategy(counterexample,
		// abstraction, taskIdentifier, emptyStackFactory, preconditionProvider);

		// to getorconstruct

		mRefinementEngine = new AutomatonFreeRefinementEngine<>(mLogger, initialStrategy);
		if (mRefinementEngine.getCounterexampleFeasibility() != LBool.UNSAT) {
			// first trace is already sat or unknown
			return;
		}

		// TODO: Start actual MCR algorithm

	}

	@Override
	public LBool isCorrect() {
		return mRefinementEngine.getCounterexampleFeasibility();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mRefinementEngine.providesIcfgProgramExecution();
	}

	@Override
	public IProgramExecution<IIcfgTransition<IcfgLocation>, Term> getRcfgProgramExecution() {
		return mRefinementEngine.getIcfgProgramExecution();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null, ExceptionHandlingCategory.KNOWN_THROW);
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		return mRefinementEngine.getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mRefinementEngine.getPredicateUnifier();
	}

	@Override
	public void aggregateStatistics(final RefinementEngineStatisticsGenerator stats) {
		// TODO: Handle statistics of nested refinement engines
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
		if (mMcr == null) {
			// TODO: Where to get a trace check factory?
			// TODO: This is only a dummy trace check factory for the initial trace

		}
		return mMcr;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		// if (mResult == null) {
		// final MCR<LETTER> mcr = mIpTcSmMCR.getOrConstruct();
		// // TODO: Are these all predicates?
		// final List<QualifiedTracePredicates> predicates = mcr.getTraceChecks().stream()
		// .map(t -> new QualifiedTracePredicates(new TracePredicates(t), t.getClass(), t.isPerfectSequence()))
		// .collect(Collectors.toList());
		// mResult = new IpAbStrategyModuleResult<>(mcr.getAutomaton(), predicates);
		// }
		// return mResult;
		throw new UnsupportedOperationException();
	}
}
