package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.McrTraceCheckResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.QualifiedTracePredicates;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.AutomatonFreeRefinementEngine;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IIpTcStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementStrategy;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.RefinementEngineStatisticsGenerator;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.Mcr.IMcrResultProvider;

public class StrategyModuleMcr<L extends IIcfgTransition<?>>
		implements IIpTcStrategyModule<Mcr<L>, L>, IIpAbStrategyModule<L>, IMcrResultProvider<L> {
	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final StrategyFactory<L> mStrategyFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private Mcr<L> mMcr;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private IpAbStrategyModuleResult<L> mAutomatonResult;
	private final List<L> mCounterexample;
	private final IAutomaton<L, IPredicate> mAbstraction;
	private final TaskIdentifier mTaskIdentifier;
	private final IInterpolantProvider<L> mInterpolantProvider;

	private final List<QualifiedTracePredicates> mUsedPredicates;
	private final IUltimateServiceProvider mServices;
	private IRefinementEngineResult<L, Collection<QualifiedTracePredicates>> mAfeResult;

	public StrategyModuleMcr(final IUltimateServiceProvider services, final ILogger logger,
			final TaCheckAndRefinementPreferences<L> prefs, final IPredicateUnifier predicateUnifier,
			final IEmptyStackStateFactory<IPredicate> emptyStackFactory, final StrategyFactory<L> strategyFactory,
			final Word<L> counterexample, final IAutomaton<L, IPredicate> abstraction,
			final TaskIdentifier taskIdentifier, final IInterpolantProvider<L> interpolantProvider) {
		mServices = services;
		mPrefs = prefs;
		mStrategyFactory = strategyFactory;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mEmptyStackFactory = emptyStackFactory;
		mCounterexample = counterexample.asList();
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		mInterpolantProvider = interpolantProvider;
		mUsedPredicates = new ArrayList<>();
	}

	@Override
	public LBool isCorrect() {
		return getOrConstruct().isCorrect();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return getOrConstruct().providesRcfgProgramExecution();
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		return getOrConstruct().getRcfgProgramExecution();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return getOrConstruct().getTraceCheckReasonUnknown();
	}

	@Override
	public IHoareTripleChecker getHoareTripleChecker() {
		getOrConstruct();
		return mAfeResult.getHoareTripleChecker();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
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
		final Mcr<L> tc = getOrConstruct();
		if (tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), true));
		}
		return Collections.emptyList();
	}

	@Override
	public Collection<QualifiedTracePredicates> getImperfectInterpolantSequences() {
		final Mcr<L> tc = getOrConstruct();
		if (!tc.isPerfectSequence()) {
			return Collections.singleton(new QualifiedTracePredicates(tc.getIpp(), tc.getClass(), false));
		}
		return Collections.emptyList();
	}

	@Override
	public Mcr<L> getOrConstruct() {
		if (mMcr == null) {
			try {
				mMcr = new Mcr<>(mServices, mLogger, mPrefs, mPredicateUnifier, mEmptyStackFactory, mCounterexample,
						mAbstraction.getAlphabet(), this, mInterpolantProvider);
			} catch (final AutomataLibraryException e) {
				throw new RuntimeException(e);
			}
		}
		return mMcr;
	}

	@Override
	public IpAbStrategyModuleResult<L> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mAutomatonResult == null) {
			mAutomatonResult = new IpAbStrategyModuleResult<>(mMcr.getAutomaton(), mUsedPredicates);
		}
		return mAutomatonResult;
	}

	@Override
	public McrTraceCheckResult<L> getResult(final Word<L> counterexample, final List<?> controlLocationSequence) {
		// Run mRefinementEngine for the given trace
		final RefinementStrategy refinementStrategy = mPrefs.getMcrRefinementStrategy();
		if (refinementStrategy == RefinementStrategy.MCR) {
			throw new IllegalStateException("MCR cannot used with MCR as internal strategy.");
		}
		final IRefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(mServices, counterexample,
				controlLocationSequence, mAbstraction, mTaskIdentifier, mEmptyStackFactory, mPredicateUnifier,
				mPredicateUnifier.getTruePredicate(), mPredicateUnifier.getFalsePredicate(), refinementStrategy);
		final AutomatonFreeRefinementEngine<L> afe = new AutomatonFreeRefinementEngine<>(mServices, mLogger, strategy);
		final List<L> trace = counterexample.asList();
		final RefinementEngineStatisticsGenerator statistics = afe.getRefinementEngineStatistics();
		mAfeResult = afe.getResult();
		final LBool feasibility = mAfeResult.getCounterexampleFeasibility();
		// We found a feasible counterexample
		if (feasibility != LBool.UNSAT) {
			return McrTraceCheckResult.constructFeasibleResult(trace, feasibility, statistics,
					mAfeResult.getIcfgProgramExecution());
		}
		// Extract interpolants, try to get a perfect sequence
		final Collection<QualifiedTracePredicates> proof = mAfeResult.getInfeasibilityProof();
		mUsedPredicates.addAll(proof);
		return McrTraceCheckResult.constructInfeasibleResult(trace, proof, statistics);
	}
}
