/*
 * Copyright (C) 2025 University of Freiburg
 * Copyright (C) 2025 LMU Munich
 * Copyright (C) 2025 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Automata Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction;

import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Set;
import java.util.concurrent.BlockingQueue;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsEmptyParallel;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;

public class CegarNWANoInterpolationWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {

	private final ILogger mLogger;
	private final TAPreferences mPref;

	private final IUltimateServiceProvider mServices;

	// SMT solver warning
	private final CfgSmtToolkit mCsToolkit;
	final PredicateFactory mPredicateFactory;
	PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;

	// globally
	protected CegarLoopStatisticsGenerator mCegarLoopBenchmark;

	// each worker needs one of their own:
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;

	// each worker needs one of their own, but creates it themself:
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult;

	TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;

	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	protected IRun<L, ?> mCounterexample = null;

	// for error automata
	private final SimplificationTechnique mSimplificationTechnique;
	private final IIcfg<? extends IcfgLocation> mIcfg;

	private final ParallelNwaCegarLoop<L, A> mMainThread;
	TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;
	INestedWordAutomaton<L, IPredicate> mAbstraction;
	private final HashMap<Integer, NestedRun<L, ?>> mCounterexamples = new HashMap<>();

	int mFoundFeasiblePaths = 0;

	/**
	 * A continues worker that addionaly searches its own counterexamples Still put the results in the result queue
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 */
	public CegarNWANoInterpolationWorkerThread(final ILogger logger, final TAPreferences pref,
			final CegarLoopResultBuilder resultBuilder, final CegarLoopStatisticsGenerator statistcs,
			final IUltimateServiceProvider services, final CfgSmtToolkit csToolkit,
			final IIcfg<? extends IcfgLocation> icfg, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils) throws InterruptedException {

		mLogger = logger;
		mPref = pref;
		mRefinementResult = null;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mCegarLoopBenchmark = statistcs;
		mServices = services;
		mCsToolkit = csToolkit;
		mIcfg = icfg;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mNwaCexTransferrer = transferWorkerUtils;
	}

	@Override
	public void run() {
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();

		// mCounterexamples.putAll(mMainThread.mActiveCounterexamples);
		int workerIterations = 0;
		try {
			mCounterexample = searchForErrorTrace();
		} catch (final AutomataOperationCanceledException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		while (!Thread.currentThread().isInterrupted()) {
			try {
				mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
				mLogger.debug("SymbolicExecutionWorker: " + mFoundFeasiblePaths);
				workerIterations += 1;
				final List<L> trace = mCounterexample.getWord().asList();
				final int traceHash = trace.hashCode();
				mLogger.info("Starting Thread: " + Thread.currentThread().getId() + "# for Trace Check: " + traceHash);
				Thread.currentThread().setName("Worker for " + traceHash);

				final var locations = getControlConfigurationsFromCounterexample(mCounterexample);
				final Counterexample<L> counterexample = new Counterexample<>(mCounterexample.getWord(), locations);
				final ITARefinementStrategy<L> strategy = setUpStrategy(counterexample);
				final LBool isCexResult = isCounterexampleFeasible(strategy);
				mLogger.debug("SAT-Worker CheckSat Done: " + isCexResult);
				if (isCexResult.equals(LBool.SAT)) {
					mFoundFeasiblePaths += 1;
					constructRefinementAutomaton(AbstractCegarLoop.AutomatonType.ERROR);
					try {
						mThreadResult = refineAbstractionInternally();
					} catch (final AutomataLibraryException e) {
						// TODO Auto-generated catch block
						throw new AssertionError(e);
					}
					mBlockingQueueForResults.put(mThreadResult);
				}

				mCounterexample = searchForErrorTrace();
				if (isCexResult.equals(LBool.SAT)) {
					// needs to be done after searching, since we are faster then the difference in main
					mCounterexamples.remove(traceHash);
				}

				boolean flag = false;
				while (mCounterexample == null) {
					mLogger.debug("--------Sat Continues Worker Stats--------");
					mLogger.debug(workerIterations);
					mLogger.info(mFoundFeasiblePaths);
					mLogger.info("SAT-Worker Going to sleep!!!");
					// wake up, if abstraction was refined, maybe there are new cex beyond the loop bound to explore
					synchronized (ParallelNwaCegarLoop.refinementLock) {
						ParallelNwaCegarLoop.refinementLock.wait();
					}
					mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
					mLogger.info("SAT-Worker wakes up and searches for new Cex.");
					mCounterexample = searchForErrorTrace();
					flag = true;
				}
				if (flag) {
					mLogger.info("SAT-Worker continues with new abstraction.");
				}

			} catch (final InterruptedException | AutomataOperationCanceledException e) {
				Thread.currentThread().interrupt();
			}
		}

	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	private INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, Mode.MAIN2WORKER);
		return workerAbstraction;
	}

	/*
	 * Search for an error trace in the current mAbstraction. First we try BFS, then IsEmptyParallel and finally DFS
	 */
	private NestedRun<L, IPredicate> searchForErrorTrace() throws AutomataOperationCanceledException {
		final Set<IPredicate> possibleEndPoints = null;
		final IsEmpty<L, IPredicate> search = getSearch(IsEmpty.SearchStrategy.PARALLEL, possibleEndPoints);
		if (isSearchCorrectAndTraceFresh(search)) {
			mLogger.debug("SymbolicExecutionWorker: Found new Counterexample via IsEmptyParallel!");
			final NestedRun<L, IPredicate> counterexample = search.getNestedRun();
			final List<L> trace = counterexample.getWord().asList();
			final int traceHash = trace.hashCode();
			if (mCounterexamples.containsKey(traceHash)) {
				throw new AssertionError("IsEmpty(Parallel) Found the same counterexample twice!");
			}
			mCounterexamples.put(traceHash, counterexample);
			return counterexample;
		}
		mLogger.debug("SymbolicExecutionWorker: Did not Find a Counterexample!");
		return null;
	}

	private IsEmpty<L, IPredicate> getSearch(final IsEmpty.SearchStrategy strategy,
			final Set<IPredicate> possibleEndPoints) throws AutomataOperationCanceledException {
		return new IsEmptyParallel<>(new AutomataLibraryServices(mServices), mAbstraction,
				mAbstraction.getInitialStates(), Collections.emptySet(), possibleEndPoints, possibleEndPoints == null,
				IsEmpty.SearchStrategy.BFS, mCounterexamples, mPref.getSearchLoopBoundForNotInterpolationWorker());

	}

	private boolean isSearchCorrectAndTraceFresh(final IsEmpty<L, IPredicate> search) {
		boolean correct = false;
		boolean fresh = true;
		try {
			correct = search.checkResult(mStateFactoryForRefinement);
		} catch (final AutomataLibraryException e) {
			e.printStackTrace();
			assert false;
		}

		final NestedRun<L, IPredicate> run = search.getNestedRun();
		if (run != null) {
			final List<L> trace = run.getWord().asList();
			final int traceHash = trace.hashCode();
			if (mCounterexamples.containsKey(traceHash)) {
				fresh = false;
			}
			return correct && fresh;
		}
		return false;
	}

	protected List<?> getControlConfigurationsFromCounterexample(final IRun<L, ?> run) {
		if (IcfgUtils.isConcurrent(mIcfg)) {
			return run.getStateSequence().stream().map(p -> ((IMLPredicate) p).getProgramPoints())
					.collect(Collectors.toList());
		}
		return getIcfgLocationsFromRun(run);
	}

	private List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) throws InterruptedException {
		final StrategyFactory<L> mStrategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mIcfg, mPredicateFactory, mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz);
		final ITARefinementStrategy<L> strategy = mStrategyFactory.constructStrategy(getServices(), counterexample,
				mAbstraction, new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, 1),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				mPref.getRefinementStrategy());
		return strategy;
	}

	private IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	private IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	protected LBool isCounterexampleFeasible(final ITARefinementStrategy<L> strategy) {
		final TraceAbstractionRefinementEngine<L> refinementEngine =
				new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy, true);
		mRefinementResult = refinementEngine.getResult();
		return mRefinementResult.getCounterexampleFeasibility();
	}

	public void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType)
			throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			constructErrorAutomaton();
			break;
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected void constructErrorAutomaton() throws AutomataOperationCanceledException {
		mErrorGeneralizationEngine.constructErrorAutomaton(mCounterexample, mPredicateFactory,
				mRefinementResult.getPredicateUnifier(), mCsToolkit, mSimplificationTechnique,
				mIcfg.getCfgSmtToolkit().getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction, 1);
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	/*
	 * Constructs only Error Automata
	 */
	public WorkerThreadResult<L, A> refineAbstractionInternally() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(1);
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;

		mErrorGeneralizationEngine.startDifference();
		automatonType = AutomatonType.ERROR;
		useErrorAutomaton = true;
		exploitSigmaStarConcatOfIa = false;
		enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
		subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
		subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult<>(
				mNwaCexTransferrer.transferAutomaton(subtrahend, mStateFactoryForRefinement, Mode.WORKER2MAIN),
				mNwaCexTransferrer.transferAutomaton(subtrahendBeforeEnhancement, mStateFactoryForRefinement,
						Mode.WORKER2MAIN),
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCsToolkit.getManagedScript(),
				mNwaCexTransferrer.transferRun((NestedRun<L, ?>) mCounterexample, Mode.WORKER2MAIN), mPredicateFactory,
				mRefinementResult.somePerfectSequenceFound(), true, false);
		return workerResult;
	}
}
