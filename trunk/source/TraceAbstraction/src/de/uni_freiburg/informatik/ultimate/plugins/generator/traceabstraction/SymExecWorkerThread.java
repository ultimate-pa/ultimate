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

import java.util.List;
import java.util.concurrent.BlockingQueue;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.IRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.TaskCanceledException.UserDefinedLimit;
import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.lib.results.UnprovabilityReason;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateUnifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.ITraceCheckStrategyModule;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils.SimplificationTechnique;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.CegarLoopResultBuilder;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.AbstractCegarLoop.Result;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.NwaCegarLoop.AutomatonType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.TransferBetweenMainAndWorker.Mode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.errorabstraction.ErrorGeneralizationEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences.InterpolantAutomatonEnhancement;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.IpTcStrategyModuleAcceleratedTraceCheck;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SymExecWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CegarLoopResultBuilder mResultBuilder;
	private final IUltimateServiceProvider mServices;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private int mIteration;
	private final ErrorGeneralizationEngine<L> mErrorGeneralizationEngine;
	private IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> mRefinementResult = null;
	private NestedWordAutomaton<L, IPredicate> mInterpolAutomaton = null;
	private IRun<L, ?> mCounterexample = null;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	private final PredicateFactoryRefinement mStateFactoryForRefinement;
	private final boolean mComputeHoareAnnotation;
	private IcfgLocation mCurrentErrorLoc;
	private final SimplificationTechnique mSimplificationTechnique;
	protected static final boolean REMOVE_DEAD_ENDS = true;
	public final ParallelNwaCegarLoop<L, A> mMainThread;
	private INestedWordAutomaton<L, IPredicate> mAbstraction;
	private StrategyFactory<L> mStrategyFactory;
	// communication with controller
	private WorkerThreadResult<L, A> mThreadResult = null;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final BlockingQueue<IRun<L, ?>> mWorkerTaskQueue;
	private final TransferBetweenMainAndWorker<L, IPredicate> mNwaCexTransferrer;

	private final PathProgramCache<L> mProgramCache;
	private final TaskIdentifier mTaskIdentifier;
	ManagedScript mMainMgdScript;

	/**
	 * CegarNwaWorkerThread is a runnable that will be executed by an executor service. It takes counterexamples from
	 * the workerTaskQueue and puts the resulting automata into the blockingQueueForResults. It takes the current
	 * abstraction from the controller, every time it does a difference calculation.
	 *
	 * TransferBetweenMainAndWorker is used to transfer between worker and controller/main cfgScript
	 *
	 * Thread-safety: everything that is given via constructor needs to be thread-save, Most things are freshly created
	 * in when the this object is created. Exceptions are: services, Preferences, the Logger and the PathProgramCache
	 * PathProgramCacheis thread save, the others shouldnt be an issue.
	 *
	 * TODO provide CEGAR loop statistics
	 *
	 * @author Max Barth (max.barth@lmu.de)
	 * @param taskIdentifier
	 */
	public SymExecWorkerThread(final ILogger logger, final TAPreferences pref, final int id,
			final CegarLoopResultBuilder resultBuilder, final IUltimateServiceProvider services,
			final CfgSmtToolkit cfgSmtToolkit, final PredicateFactory predicateFactory,
			final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final PredicateFactoryRefinement stateFactoryForRefinement, final boolean computeHoareAnnotation,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final BlockingQueue<IRun<L, ?>> workerTaskQueue,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils, final TaskIdentifier taskIdentifier)
			throws InterruptedException {

		mLogger = logger;
		mPref = pref;
		mIteration = id;
		mResultBuilder = resultBuilder;
		mErrorGeneralizationEngine = new ErrorGeneralizationEngine<>(services);
		mServices = services;
		mCfgSmtToolkit = cfgSmtToolkit;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactory = predicateFactory;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mStateFactoryForRefinement = stateFactoryForRefinement;
		mComputeHoareAnnotation = computeHoareAnnotation;
		mSimplificationTechnique = pref.getSimplificationTechnique();
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mWorkerTaskQueue = workerTaskQueue;
		mNwaCexTransferrer = transferWorkerUtils;
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAbstraction();
		mTaskIdentifier = taskIdentifier;
		mProgramCache = new PathProgramCache<>(mLogger);
		mMainMgdScript = mainThread.mCsToolkit.getManagedScript();
	}

	/*
	 * Gets a counterexamples from the blocking queue, sets up a strategy (checks how often the pathprogram has been
	 * seen). Checks feasibility, interpolates, creates an Error or Interpolant automaton. Calculates the difference to
	 * generalize the interpolant automaton and then puts a @WorkerThreadResult into the blocking queue for results.
	 *
	 * Terminates if the Thread is interrupted (not used atm) or the Executioner service triggers a shutdown.
	 */
	@Override
	public void run() {
		Thread.currentThread().setName("Sym Exec Thread");
		while (!Thread.currentThread().isInterrupted()) {
			try {
				mLogger.info("WorkerThread for Symbolic Execution Starts");
				mIteration = 1;

				final boolean safe = runSymExec();
				if (safe) {
					mBlockingQueueForResults.put(new WorkerThreadResult<>(null, null, null, false, null, false, null,
							null, null, null, false));
					return;
				} else {
					return;
				}

			} catch (final InterruptedException e) {
				Thread.currentThread().interrupt();
			} catch (final Throwable t) {
				try {
					mBlockingQueueForResults.put(new WorkerThreadResult<>(null, null, null, false, null, false, null,
							null, null, null, true));
				} catch (final InterruptedException ie) {
					Thread.currentThread().interrupt();
				}
				return;
			}
		}
	}

	private boolean runSymExec() throws AutomataLibraryException, InterruptedException {
		final SymbolicExecution symbolicExecution = new SymbolicExecution(mServices, mLogger,
				mTaCheckAndRefinementPrefs, mCfgSmtToolkit, mMainMgdScript, mAbstraction, mTaskIdentifier, this, mPref);
		if (symbolicExecution.isSafe() && !symbolicExecution.wasOverapproximated()) {
			return true;
		} else if (!symbolicExecution.isSafe() && !symbolicExecution.wasUnkown()) {
			mCounterexample = mNwaCexTransferrer.transferRun(symbolicExecution.getCounterexample(),
					TransferBetweenMainAndWorker.Mode.MAIN2WORKER);
			return false;
		} else {
			throw new AssertionError("Loop Bound");
		}
	}

	public void constructErrorAutomatonAndPutItInQueue(final IRun<L, ?> counterexampleWorker)
			throws InterruptedException {
		try {
			final IRun<L, ?> counterexample = mNwaCexTransferrer.transferRun((NestedRun<L, ?>) counterexampleWorker,
					TransferBetweenMainAndWorker.Mode.MAIN2WORKER);
			mAbstraction = (INestedWordAutomaton<L, IPredicate>) getAndTransferAbstraction();
			final var locations = getControlConfigurationsFromCounterexample(counterexample);
			final Counterexample<L> cex = new Counterexample<>(counterexample.getWord(), locations);
			final ITARefinementStrategy<L> strategy = setUpStrategy(cex);
			final Pair<LBool, IProgramExecution<L, Term>> isCexResult =
					isCounterexampleFeasible(strategy, counterexample);
			assert isCexResult.getFirst().equals(LBool.SAT);
			final AbstractCegarLoop.AutomatonType automatonType = processFeasibilityCheckResult(strategy,
					isCexResult.getFirst(), isCexResult.getSecond(), mCurrentErrorLoc);
			constructRefinementAutomaton(automatonType, counterexample);
			mThreadResult = refineAbstractionInternally();
		} catch (AutomataLibraryException | ToolchainCanceledException | SMTLIBException e) {
			throw new AssertionError("WorkerThread Failed: " + e);
		}
		mBlockingQueueForResults.put(mThreadResult);
	}

	private IPredicateUnifier constructPredicateUnifier(final IUltimateServiceProvider services) {
		final ManagedScript managedScript = mCfgSmtToolkit.getManagedScript();
		final IIcfgSymbolTable symbolTable = mCfgSmtToolkit.getSymbolTable();

		return new PredicateUnifier(mLogger, services, managedScript, mPredicateFactory, symbolTable, null);
	}

	protected List<?> getControlConfigurationsFromCounterexample(final IRun<L, ?> run) {
		return getIcfgLocationsFromRun(run);
	}

	private List<IcfgLocation> getIcfgLocationsFromRun(final IRun<L, ?> run) {
		return run.getStateSequence().stream().map(p -> ((ISLPredicate) p).getProgramPoint())
				.collect(Collectors.toList());
	}

	private ITARefinementStrategy<L> setUpStrategy(final Counterexample<L> counterexample) {
		mStrategyFactory = new StrategyFactory(mLogger, mPref, mTaCheckAndRefinementPrefs, mCfgSmtToolkit,
				mPredicateFactory, mPredicateFactoryInterpolantAutomata, mMainThread.mTransitionClazz, mProgramCache);

		final ITARefinementStrategy<L> strategy;
		strategy = mStrategyFactory.constructStrategy(getServices(), counterexample, mAbstraction,
				new SubtaskIterationIdentifier(mMainThread.mTaskIdentifier, mIteration),
				mPredicateFactoryInterpolantAutomata, getPreconditionProvider(), getPostconditionProvider(),
				mPref.getRefinementStrategy());
		return strategy;
	}

	/**
	 * Worker takes the current abstraction from the main thread (read only). Then transfers it to worker script.
	 */
	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
//		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
//				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, Mode.MAIN2WORKER);
		return mainAbstraction;
	}

	public INwaOutgoingLetterAndTransitionProvider<L, IPredicate> getAndTransferAbstraction() {
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> mainAbstraction = mMainThread.getAbstraction();
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> workerAbstraction = mNwaCexTransferrer
				.transferAutomaton(mainAbstraction, mPredicateFactoryInterpolantAutomata, Mode.MAIN2WORKER);
		return workerAbstraction;
	}

	private IPreconditionProvider getPreconditionProvider() {
		return IPreconditionProvider.constructDefaultPreconditionProvider();
	}

	private IPostconditionProvider getPostconditionProvider() {
		return IPostconditionProvider.constructDefaultPostconditionProvider();
	}

	protected Pair<LBool, IProgramExecution<L, Term>> isCounterexampleFeasible(final ITARefinementStrategy<L> strategy,
			final IRun<L, ?> counterexample) {
		try {
			if (mPref.hasLimitPathProgramCount() && mPref.getLimitPathProgramCount() < mStrategyFactory
					.getPathProgramCache().getPathProgramCount(mCounterexample.getWord())) {
				final String taskDescription = "bailout by path program count limit in iteration " + mIteration;
				throw new TaskCanceledException(UserDefinedLimit.PATH_PROGRAM_ATTEMPTS, getClass(), taskDescription);
			}

			final TraceAbstractionRefinementEngine<L> refinementEngine =
					new TraceAbstractionRefinementEngine<>(getServices(), mLogger, strategy);
			mRefinementResult = refinementEngine.getResult();

		} catch (final ToolchainCanceledException | SMTLIBException tce) {
			throw tce;
		}
		final LBool feasibility = mRefinementResult.getCounterexampleFeasibility();
		IProgramExecution<L, Term> rcfgProgramExecution = null;
		if (feasibility != LBool.UNSAT) {
			mLogger.info("Counterexample %s feasible", feasibility == LBool.SAT ? "is" : "might be");
			if (mRefinementResult.providesIcfgProgramExecution()) {
				rcfgProgramExecution = mRefinementResult.getIcfgProgramExecution();
			} else {
				rcfgProgramExecution =
						TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(counterexample.getWord());
			}
			((IcfgProgramExecution<L>) rcfgProgramExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());
		}
		// TODO use some kind of mCegarLoopBenchmark (currently leads to concurrency problems)
		return new Pair<>(feasibility, rcfgProgramExecution);
	}

	/**
	 * Report results from a feasibility check if necessary and return the type of the refinement automaton
	 *
	 * @param strategy
	 */
	private AbstractCegarLoop.AutomatonType processFeasibilityCheckResult(final ITARefinementStrategy<L> strategy,
			final LBool isCounterexampleFeasible, final IProgramExecution<L, Term> programExecution,
			final IcfgLocation currentErrorLoc) {
		if (isCounterexampleFeasible == Script.LBool.SAT) {
			mResultBuilder.addResultForProgramExecution(Result.UNSAFE, programExecution, null, null);
			if (mPref.stopAfterFirstViolation()) {
				mResultBuilder.addResultForAllRemaining(Result.UNKNOWN);
			}
			return AbstractCegarLoop.AutomatonType.ERROR;
		}
		assert isCounterexampleFeasible != Script.LBool.UNKNOWN;
		Result actualResult;
		if (programExecution != null) {
			for (final ITraceCheckStrategyModule<L, ?> module : strategy.getTraceCheckModules()) {
				if (module instanceof IpTcStrategyModuleAcceleratedTraceCheck) {
					throw new AssertionError(
							"TraceCheck Unknown, dont return result. Might be just this Strategy that fails");
				}
			}
			final UnprovabilityReason reasonUnknown =
					new UnprovabilityReason("unable to decide satisfiability of path constraint");
			actualResult = Result.UNKNOWN;
			mResultBuilder.addResultForProgramExecution(actualResult, programExecution, null, reasonUnknown);
		}
		actualResult = Result.TIMEOUT;
		mResultBuilder.addResult(currentErrorLoc, actualResult, null, null, null);

		if (mPref.stopAfterFirstViolation()) {
			mResultBuilder.addResultForAllRemaining(actualResult);
		}

		return AbstractCegarLoop.AutomatonType.UNKNOWN;
	}

	/**
	 * This Method does not do the sanity checks done in NWA for the correctness of Error and Interpolant automata!
	 *
	 * @param automatonType
	 * @param counterexample
	 * @throws AutomataOperationCanceledException
	 */
	private void constructRefinementAutomaton(final AbstractCegarLoop.AutomatonType automatonType,
			final IRun<L, ?> counterexample) throws AutomataOperationCanceledException {
		switch (automatonType) {
		case ERROR:
		case UNKNOWN:
			mLogger.info("Excluding counterexample to continue analysis with %s automaton", automatonType);
			mErrorGeneralizationEngine.constructErrorAutomaton(counterexample, mPredicateFactory,
					mRefinementResult.getPredicateUnifier(), mCfgSmtToolkit, mSimplificationTechnique,
					mCfgSmtToolkit.getSymbolTable(), mPredicateFactoryInterpolantAutomata, mAbstraction, mIteration);
			mInterpolAutomaton = null;
			break;
		case INTERPOLANT:
		default:
			throw new UnsupportedOperationException("Unknown automaton type: " + automatonType);
		}
	}

	protected IUltimateServiceProvider getServices() {
		return mServices;
	}

	private WorkerThreadResult<L, A> refineAbstractionInternally() throws AutomataLibraryException {
		mStateFactoryForRefinement.setIteration(mIteration);
		// mCegarLoopBenchmark.start(CegarLoopStatisticsDefinitions.AutomataDifference.toString());
		final IPredicateUnifier predicateUnifier = mRefinementResult.getPredicateUnifier();

		final AutomatonType automatonType;
		final boolean useErrorAutomaton;
		final NestedWordAutomaton<L, IPredicate> subtrahendBeforeEnhancement;
		final InterpolantAutomatonEnhancement enhanceMode;
		final INwaOutgoingLetterAndTransitionProvider<L, IPredicate> subtrahend;
		final boolean exploitSigmaStarConcatOfIa;
		assert mErrorGeneralizationEngine.hasAutomatonInIteration(mIteration);
		mErrorGeneralizationEngine.startDifference();
		automatonType = AutomatonType.ERROR;
		useErrorAutomaton = true;
		exploitSigmaStarConcatOfIa = false;
		enhanceMode = mErrorGeneralizationEngine.getEnhancementMode();
		subtrahendBeforeEnhancement = mErrorGeneralizationEngine.getResultBeforeEnhancement();
		subtrahend = mErrorGeneralizationEngine.getResultAfterEnhancement();

		final WorkerThreadResult<L, A> workerResult = new WorkerThreadResult(
				mNwaCexTransferrer.transferAutomaton(subtrahend, mPredicateFactoryInterpolantAutomata,
						Mode.WORKER2MAIN),
				mNwaCexTransferrer.transferAutomaton(subtrahendBeforeEnhancement, mPredicateFactoryInterpolantAutomata,
						Mode.WORKER2MAIN),
				predicateUnifier, exploitSigmaStarConcatOfIa, enhanceMode, useErrorAutomaton, automatonType,
				mCfgSmtToolkit.getManagedScript(), null, mPredicateFactory, false);
		return workerResult;
	}

}