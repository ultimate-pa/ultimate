package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Difference;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.mcr.IInterpolantProvider;
import de.uni_freiburg.informatik.ultimate.lib.mcr.McrAutomatonBuilder;
import de.uni_freiburg.informatik.ultimate.lib.mcr.McrTraceCheckResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.HoareTripleCheckerUtils.HoareTripleChecks;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.hoaretriple.IHoareTripleChecker;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.IInterpolatingTraceCheck;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.interpolant.InterpolantComputationStatus.ItpErrorStatus;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.ITraceCheckPreferences;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.ExceptionHandlingCategory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.tracecheck.TraceCheckReasonUnknown.Reason;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryRefinement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.interpolantautomata.transitionappender.DeterministicInterpolantAutomaton;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public class Mcr<L extends IIcfgTransition<?>> implements IInterpolatingTraceCheck<L> {
	private final ILogger mLogger;
	private final IPredicateUnifier mPredicateUnifier;
	private final IUltimateServiceProvider mServices;
	private final AutomataLibraryServices mAutomataServices;
	private final CfgSmtToolkit mToolkit;
	private final IEmptyStackStateFactory<IPredicate> mEmptyStackStateFactory;
	private final VpAlphabet<L> mAlphabet;
	private final IMcrResultProvider<L> mResultProvider;
	private final IHoareTripleChecker mHoareTripleChecker;
	private final IInterpolantProvider<L> mInterpolantProvider;

	private final McrTraceCheckResult<L> mResult;

	public Mcr(final IUltimateServiceProvider services, final ILogger logger, final ITraceCheckPreferences prefs,
			final IPredicateUnifier predicateUnifier, final IEmptyStackStateFactory<IPredicate> emptyStackStateFactory,
			final List<L> trace, final Set<L> alphabet, final IMcrResultProvider<L> resultProvider,
			final IInterpolantProvider<L> interpolantProvider) throws AutomataLibraryException {
		mLogger = logger;
		mPredicateUnifier = predicateUnifier;
		mServices = services;
		mAutomataServices = new AutomataLibraryServices(mServices);
		mAlphabet = new VpAlphabet<>(alphabet);
		mToolkit = prefs.getCfgSmtToolkit();
		mEmptyStackStateFactory = emptyStackStateFactory;
		mResultProvider = resultProvider;
		mHoareTripleChecker = HoareTripleCheckerUtils.constructEfficientHoareTripleCheckerWithCaching(mServices,
				HoareTripleChecks.INCREMENTAL, mToolkit, mPredicateUnifier);
		mInterpolantProvider = interpolantProvider;
		// Explore all the interleavings of trace
		mResult = exploreInterleavings(trace);
	}

	private McrTraceCheckResult<L> exploreInterleavings(final List<L> initialTrace) throws AutomataLibraryException {
		final ManagedScript managedScript = mToolkit.getManagedScript();
		final McrAutomatonBuilder<L> automatonBuilder = new McrAutomatonBuilder<>(initialTrace, mPredicateUnifier,
				mEmptyStackStateFactory, mLogger, mAlphabet, mServices);
		final PredicateFactory predicateFactory =
				new PredicateFactory(mServices, managedScript, mToolkit.getSymbolTable());
		final PredicateFactoryRefinement factory = new PredicateFactoryRefinement(mServices, managedScript,
				predicateFactory, false, Collections.emptySet());
		final List<INestedWordAutomaton<L, IPredicate>> automata = new ArrayList<>();
		INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mhbAutomaton =
				automatonBuilder.buildMhbAutomaton(predicateFactory);
		NestedRun<L, ?> counterexample = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		int iteration = 0;
		McrTraceCheckResult<L> result = null;
		while (counterexample != null) {
			mLogger.info("---- MCR iteration " + iteration + " ----");
			iteration++;
			result = mResultProvider.getResult(counterexample);
			final List<L> trace = counterexample.getWord().asList();
			if (result.isCorrect() != LBool.UNSAT) {
				// We found a feasible error trace
				return result;
			}
			final INestedWordAutomaton<L, IPredicate> automaton = automatonBuilder.buildInterpolantAutomaton(trace,
					Arrays.asList(result.getInterpolants()), mInterpolantProvider);
			final DeterministicInterpolantAutomaton<L> ipAutomaton = new DeterministicInterpolantAutomaton<>(mServices,
					mToolkit, mHoareTripleChecker, automaton, mPredicateUnifier, false, false);
			// TODO: Add ipAutomaton instead?
			automata.add(automaton);
			mhbAutomaton = new Difference<>(mAutomataServices, factory, mhbAutomaton, ipAutomaton).getResult();
			counterexample = new IsEmpty<>(mAutomataServices, mhbAutomaton).getNestedRun();
		}
		// All interleavings are infeasible, therefore create an interpolant automaton
		result.setAutomaton(unionAutomata(automata));
		return result;
	}

	private NestedWordAutomaton<L, IPredicate> unionAutomata(final List<INestedWordAutomaton<L, IPredicate>> automata) {
		final NestedWordAutomaton<L, IPredicate> result =
				new NestedWordAutomaton<>(mAutomataServices, mAlphabet, mEmptyStackStateFactory);
		final IPredicate truePredicate = mPredicateUnifier.getTruePredicate();
		result.addState(true, false, truePredicate);
		result.addState(false, true, mPredicateUnifier.getFalsePredicate());
		for (final INestedWordAutomaton<L, IPredicate> a : automata) {
			final LinkedList<IPredicate> queue = new LinkedList<>();
			final Set<IPredicate> visited = new HashSet<>();
			queue.add(truePredicate);
			while (!queue.isEmpty()) {
				final IPredicate state = queue.remove();
				if (!visited.add(state)) {
					continue;
				}
				for (final OutgoingInternalTransition<L, IPredicate> edge : a.internalSuccessors(state)) {
					final IPredicate succ = edge.getSucc();
					if (!result.contains(succ)) {
						result.addState(false, false, succ);
					}
					result.addInternalTransition(state, edge.getLetter(), succ);
					queue.add(succ);
				}
			}
		}
		return result;
	}

	public NestedWordAutomaton<L, IPredicate> getAutomaton() {
		return mResult.getAutomaton();
	}

	@Override
	public List<L> getTrace() {
		return mResult.getTrace();
	}

	@Override
	public IPredicate[] getInterpolants() {
		return mResult.getInterpolants();
	}

	@Override
	public IPredicateUnifier getPredicateUnifier() {
		return mPredicateUnifier;
	}

	@Override
	public boolean isPerfectSequence() {
		// TODO: Adapt later; for now, automata are created by MCR so it does not really matter
		return false;
	}

	@Override
	public InterpolantComputationStatus getInterpolantComputationStatus() {
		switch (isCorrect()) {
		case UNSAT:
			return new InterpolantComputationStatus();
		case SAT:
			return new InterpolantComputationStatus(ItpErrorStatus.TRACE_FEASIBLE, null);
		default:
			throw new UnsupportedOperationException();
		}
	}

	@Override
	public LBool isCorrect() {
		return mResult.isCorrect();
	}

	@Override
	public IPredicate getPrecondition() {
		return mPredicateUnifier.getTruePredicate();
	}

	@Override
	public IPredicate getPostcondition() {
		return mPredicateUnifier.getFalsePredicate();
	}

	@Override
	public Map<Integer, IPredicate> getPendingContexts() {
		return Collections.emptyMap();
	}

	@Override
	public boolean providesRcfgProgramExecution() {
		return mResult.providesExecution();
	}

	@Override
	public IProgramExecution<L, Term> getRcfgProgramExecution() {
		return mResult.getExecution();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mResult.getStatistics();
	}

	@Override
	public TraceCheckReasonUnknown getTraceCheckReasonUnknown() {
		return new TraceCheckReasonUnknown(Reason.SOLVER_RESPONSE_OTHER, null, ExceptionHandlingCategory.KNOWN_THROW);
	}

	@Override
	public boolean wasTracecheckFinishedNormally() {
		// TODO Auto-generated method stub
		return true;
	}

	public interface IMcrResultProvider<LETTER extends IIcfgTransition<?>> {
		McrTraceCheckResult<LETTER> getResult(Word<LETTER> counterexample, List<?> controlLocationSequence);
	}
}
