package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.Collection;
import java.util.Collections;
import java.util.List;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.mcr.MCR;
import de.uni_freiburg.informatik.ultimate.lib.mcr.StatelessRun;
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.RefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class StrategyModuleMcr<LETTER extends IIcfgTransition<?>> implements IIpTcStrategyModule<MCR<LETTER>, LETTER>,
		IIpAbStrategyModule<LETTER>, Function<List<LETTER>, Pair<LBool, IPredicate[]>> {

	private final ILogger mLogger;
	private final TaCheckAndRefinementPreferences<?> mPrefs;
	private final StrategyFactory<LETTER> mStrategyFactory;
	private final IPredicateUnifier mPredicateUnifier;
	private MCR<LETTER> mMcr;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackFactory;
	private AutomatonFreeRefinementEngine<LETTER> mRefinementEngine;
	private IpAbStrategyModuleResult<LETTER> mAutomatonResult;
	private final List<LETTER> mCounterexample;
	private final IAutomaton<LETTER, IPredicate> mAbstraction;
	private final TaskIdentifier mTaskIdentifier;

	public StrategyModuleMcr(final ILogger logger, final TaCheckAndRefinementPreferences<LETTER> prefs,
			final IPredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> emptyStackFactory,
			final StrategyFactory<LETTER> strategyFactory, final IRun<LETTER, ?> counterexample,
			final IAutomaton<LETTER, IPredicate> abstraction, final TaskIdentifier taskIdentifier) {
		mPrefs = prefs;
		mStrategyFactory = strategyFactory;
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mEmptyStackFactory = emptyStackFactory;
		mCounterexample = counterexample.getWord().asList();
		mAbstraction = abstraction;
		mTaskIdentifier = taskIdentifier;
		runEngine(mCounterexample);
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
			try {
				mMcr = new MCR<>(mLogger, mPrefs, mPredicateUnifier, mEmptyStackFactory, mCounterexample, this);
			} catch (final AutomataLibraryException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		}
		return mMcr;
	}

	@Override
	public IpAbStrategyModuleResult<LETTER> buildInterpolantAutomaton(final List<QualifiedTracePredicates> perfectIpps,
			final List<QualifiedTracePredicates> imperfectIpps) throws AutomataOperationCanceledException {
		if (mAutomatonResult == null) {
			// TODO: What are the predicates?
			mAutomatonResult = new IpAbStrategyModuleResult<>(mMcr.getAutomaton(), null);
		}
		return mAutomatonResult;
	}

	@Override
	public Pair<LBool, IPredicate[]> apply(final List<LETTER> trace) {
		runEngine(trace);
		final LBool feasibility = mRefinementEngine.getCounterexampleFeasibility();
		if (feasibility != LBool.UNSAT) {
			return new Pair<>(feasibility, null);
		}
		// Extract interpolants, try to get a perfect sequence
		final Collection<QualifiedTracePredicates> proves = mRefinementEngine.getInfeasibilityProof();
		QualifiedTracePredicates resultProof = proves.iterator().next();
		for (final QualifiedTracePredicates proof : proves) {
			if (proof.isPerfect()) {
				resultProof = proof;
				break;
			}
		}
		final List<IPredicate> predicates = resultProof.getPredicates();
		return new Pair<>(feasibility, predicates.toArray(new IPredicate[predicates.size()]));
	}

	private void runEngine(final List<LETTER> trace) {
		final IRun<LETTER, ?> run = new StatelessRun<>(TraceCheckUtils.toNestedWord(mCounterexample));
		// Run mRefinementEngine for the given trace
		final RefinementStrategy refinementStrategy = mPrefs.getMcrRefinementStrategy();
		if (refinementStrategy == RefinementStrategy.MCR) {
			throw new IllegalStateException("MCR cannot used with MCR as internal strategy.");
		}
		final IRefinementStrategy<LETTER> strategy =
				mStrategyFactory.constructStrategy(run, mAbstraction, mTaskIdentifier, mEmptyStackFactory,
						IPreconditionProvider.constructDefaultPreconditionProvider(), refinementStrategy);
		mRefinementEngine = new AutomatonFreeRefinementEngine<>(mLogger, strategy);
	}
}
