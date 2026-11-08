/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.valueanalysis;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.BlockingQueue;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedRun;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressMonitorService;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.translation.IProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.CfgSmtToolkit;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgProgramExecution;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.ISLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.SubtaskIterationIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.taskidentifier.TaskIdentifier;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.tracehandling.IRefinementEngineResult;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.Counterexample;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.singletracecheck.TraceCheckUtils;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteConfiguration;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteNwaSemantics;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteTransFormulaExecutor;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.NondeterminismPool;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPostconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.IPreconditionProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PathProgramCache;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.PredicateFactoryForInterpolantAutomata;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ICegarNwaWorkerThread;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.ParallelNwaCegarLoop;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.RetirementTimer;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TaskScopedServices;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker.TransferMode;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.TransferBetweenMainAndWorker;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult.WorkerType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.WorkerThreadResult;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TAPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.preferences.TraceAbstractionPreferenceInitializer.ValueAnalysisSearch;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.StrategyFactory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TaCheckAndRefinementPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine.ITARefinementStrategy;
import de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.tracehandling.TraceAbstractionRefinementEngine;

/**
 * Worker thread inside {@link ParallelNwaCegarLoop} that looks for a violation cheaply: it executes the program
 * concretely, in plain Java and without the solver, on the initial abstraction (the program as nested word automaton),
 * see {@link ConcreteNwaSemantics}. It under-approximates, so it can only ever show that a program is unsafe.
 * <p>
 * When the search reaches an error location, the run that led there goes through the same refinement engine
 * {@code CegarNwaWorkerThread} uses. That single trace check is the worker's only solver call per violation; it
 * confirms the run and yields a program execution with values. The worker then hands the main thread a
 * {@link WorkerThreadResult#violation} result, and the main thread registers it.
 * <p>
 * Whenever the worker finds nothing, because the search ended, its time limit ran out, it was retired, or anything
 * went wrong, it ends with the result UNKNOWN: a {@link WorkerThreadResult#noVerdict} result, which the main thread
 * only logs. It never posts a crash and it does not count among the workers whose retirement makes the whole loop
 * UNKNOWN, so the other workers go on deciding the program. It runs outside the loop's worker pool and does not count
 * towards the thread limit.
 *
 * @author Max Barth (max.barth@lmu.de)
 */
public class ValueAnalysisWorkerThread<L extends IIcfgTransition<?>, A extends IAutomaton<L, IPredicate>>
		implements ICegarNwaWorkerThread<L, A> {
	private final ILogger mLogger;
	private final TAPreferences mPref;
	private final CfgSmtToolkit mCfgSmtToolkit;
	private final PredicateFactory mPredicateFactory;
	private final PredicateFactoryForInterpolantAutomata mPredicateFactoryInterpolantAutomata;
	private final TaCheckAndRefinementPreferences<L> mTaCheckAndRefinementPrefs;
	private final ParallelNwaCegarLoop<L, A> mMainThread;
	private final INestedWordAutomaton<L, IPredicate> mAbstraction;
	private final BlockingQueue<WorkerThreadResult<L, A>> mBlockingQueueForResults;
	private final TaskIdentifier mTaskIdentifier;
	// Only used to build a refinement strategy for a counterexample; this worker has no path-program history.
	private final PathProgramCache<L> mProgramCache;
	private final IUltimateServiceProvider mParentServices;
	// Stops the search and the trace check when the HeapWatchdog retires the worker, via the progress monitor of
	// mServices, which also asks the time limit.
	private final RetirementTimer mRetirementTimer;
	// Both set when the worker starts, so that its time limit counts from then
	private IUltimateServiceProvider mServices;
	private long mTimeLimitDeadline;
	private final ConcreteTransFormulaExecutor mExecutor;
	private final IConcreteSearchStrategy<L> mSearch;

	private int mTraceChecks;
	private IProgramExecution<L, Term> mViolation;

	public ValueAnalysisWorkerThread(final ILogger logger, final TAPreferences pref,
			final IUltimateServiceProvider services, final CfgSmtToolkit cfgSmtToolkit,
			final PredicateFactory predicateFactory, final TaCheckAndRefinementPreferences<L> taCheckAndRefinementPrefs,
			final PredicateFactoryForInterpolantAutomata predicateFactoryInterpolantAutomata,
			final ParallelNwaCegarLoop<L, A> mainThread,
			final BlockingQueue<WorkerThreadResult<L, A>> blockingQueueForResults,
			final TransferBetweenMainAndWorker<L, IPredicate> transferWorkerUtils,
			final TaskIdentifier taskIdentifier, final RetirementTimer retirementTimer) {
		mLogger = logger;
		mPref = pref;
		mCfgSmtToolkit = cfgSmtToolkit;
		mPredicateFactory = predicateFactory;
		mTaCheckAndRefinementPrefs = taCheckAndRefinementPrefs;
		mPredicateFactoryInterpolantAutomata = predicateFactoryInterpolantAutomata;
		mMainThread = mainThread;
		mBlockingQueueForResults = blockingQueueForResults;
		mTaskIdentifier = taskIdentifier;
		mProgramCache = new PathProgramCache<>(mLogger);
		// Runs on the main thread, before the loop refines anything: this is the initial abstraction, the program.
		mAbstraction = (INestedWordAutomaton<L, IPredicate>) transferWorkerUtils.transferAutomaton(
				mainThread.getAbstraction(), mPredicateFactoryInterpolantAutomata, TransferMode.MAIN2WORKER);
		mParentServices = services;
		mRetirementTimer = retirementTimer;
		mExecutor = new ConcreteTransFormulaExecutor(new NondeterminismPool(), pref.getValueAnalysisMaxChoices());
		mSearch = createSearch(pref.getValueAnalysisSearch());
	}

	private static <L extends IIcfgTransition<?>> IConcreteSearchStrategy<L>
			createSearch(final ValueAnalysisSearch search) {
		switch (search) {
		case BFS:
			return new BreadthFirstConcreteSearch<>();
		default:
			throw new AssertionError("unknown value analysis search " + search);
		}
	}

	@Override
	public void run() {
		Thread.currentThread().setName("Value Analysis Thread");
		final long timeLimit = mPref.getValueAnalysisTimeLimit() * 1000L;
		final IProgressMonitorService progressMonitor = mParentServices.getProgressMonitorService();
		mTimeLimitDeadline = System.currentTimeMillis() + timeLimit;
		mServices = progressMonitor.registerChildTimer(mParentServices, mRetirementTimer.getChildTimer(timeLimit));
		try {
			mLogger.info("Value analysis: starts, search %s, time limit %d s", mPref.getValueAnalysisSearch(),
					mPref.getValueAnalysisTimeLimit());
			final ConcreteNwaSemantics<L> semantics =
					new ConcreteNwaSemantics<>(mAbstraction, mCfgSmtToolkit.getModifiableGlobalsTable(), mExecutor);
			final ConcreteConfiguration<L> violation = mSearch.search(semantics, this::keepGoing,
					configuration -> confirm(semantics.toNestedRun(configuration)));
			if (violation != null) {
				mLogger.info("Value analysis: confirmed a violation of %d letter(s)", violation.getLength());
				mBlockingQueueForResults.put(WorkerThreadResult.violation(WorkerType.VALUE_ANALYSIS, mViolation));
			} else if (!stoppedFromOutside()) {
				finishUnknown(budgetMessage("found no violation"));
			}
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		} catch (final Throwable t) {
			if (stoppedFromOutside()) {
				mLogger.info("Value analysis: stopping, shut down during a trace check (" + t + ")");
			} else if (timeLimitReached() || mRetirementTimer.isRetired()) {
				// A cancellation, or an exception that wraps one: the time limit or the retirement stopped it.
				finishUnknown(budgetMessage(null));
			} else {
				// Never a crash of the loop: the other workers decide the program without us.
				mLogger.error("Value analysis: stopped by " + t);
				for (final StackTraceElement element : t.getStackTrace()) {
					mLogger.error("\tat " + element);
				}
				finishUnknown("stopped by " + t);
			}
		} finally {
			mLogger.info("Value analysis: %s; %d step(s) executed, %d lost successors to unsupported terms, %d to "
					+ "the choice limit; %d trace check(s)", mSearch.getStatistics(), mExecutor.getSteps(),
					mExecutor.getUnsupportedSteps(), mExecutor.getTruncatedSteps(), mTraceChecks);
			mRetirementTimer.stopped();
		}
	}

	/**
	 * Ends the worker with the result UNKNOWN. The main thread only logs it; the other workers go on.
	 *
	 * @param reason
	 *            why the worker found no violation, for the log
	 */
	private void finishUnknown(final String reason) {
		mLogger.info("Value analysis: %s; result UNKNOWN, the other workers go on", reason);
		try {
			mBlockingQueueForResults.put(WorkerThreadResult.noVerdict(WorkerType.VALUE_ANALYSIS));
		} catch (final InterruptedException e) {
			Thread.currentThread().interrupt();
		}
	}

	/**
	 * @return whether the loop shut the worker down, so that nobody waits for its result any more
	 */
	private boolean stoppedFromOutside() {
		return mMainThread.isShuttingDown() || Thread.currentThread().isInterrupted();
	}

	private boolean timeLimitReached() {
		return System.currentTimeMillis() >= mTimeLimitDeadline;
	}

	/**
	 * @return whether the worker was retired or reached its time limit, or {@code otherwise} if neither
	 */
	private String budgetMessage(final String otherwise) {
		if (mRetirementTimer.isRetired()) {
			return "retired, " + mRetirementTimer.getReason();
		}
		if (timeLimitReached()) {
			return String.format("reached its time limit of %d s", mPref.getValueAnalysisTimeLimit());
		}
		return otherwise;
	}

	private boolean keepGoing() {
		return !Thread.currentThread().isInterrupted() && !mMainThread.isShuttingDown()
				&& mServices.getProgressMonitorService().continueProcessing();
	}

	/**
	 * Checks the run with the refinement engine, as {@code CegarNwaWorkerThread} checks a counterexample, so that the
	 * program execution carries variable values and backtranslates to the input program like any other.
	 *
	 * @return whether the trace check confirmed the run; if so, {@link #mViolation} is its program execution
	 */
	private boolean confirm(final NestedRun<L, IPredicate> run) {
		final List<IcfgLocation> locations = new ArrayList<>();
		for (final IPredicate state : run.getStateSequence()) {
			if (!(state instanceof final ISLPredicate slPredicate)) {
				mLogger.warn("Value analysis: abstraction state %s is a %s, not an ISLPredicate, so it has no program "
						+ "point; the run is not checked", state, state.getClass().getSimpleName());
				return false;
			}
			locations.add(slPredicate.getProgramPoint());
		}
		mTraceChecks++;
		mLogger.info("Value analysis: reached an error location with a run of %d letter(s), checking it",
				run.getWord().length());
		final Counterexample<L> cex = new Counterexample<>(run.getWord(), locations);
		// The solvers of this trace check end with it, otherwise every checked run would leave a solver process.
		final TaskScopedServices checkServices = new TaskScopedServices(mServices);
		try {
			return confirm(run, cex, checkServices);
		} finally {
			checkServices.destroyAll(mLogger);
		}
	}

	private boolean confirm(final NestedRun<L, IPredicate> run, final Counterexample<L> cex,
			final IUltimateServiceProvider checkServices) {
		final StrategyFactory<L> strategyFactory = new StrategyFactory<>(mLogger, mPref, mTaCheckAndRefinementPrefs,
				mCfgSmtToolkit, mPredicateFactory, mPredicateFactoryInterpolantAutomata,
				mMainThread.mTransitionClazz, mProgramCache);
		final ITARefinementStrategy<L> strategy = strategyFactory.constructStrategy(checkServices, cex, mAbstraction,
				new SubtaskIterationIdentifier(mTaskIdentifier, mTraceChecks), mPredicateFactoryInterpolantAutomata,
				IPreconditionProvider.constructDefaultPreconditionProvider(),
				IPostconditionProvider.constructDefaultPostconditionProvider(), mPref.getRefinementStrategy());
		final IRefinementEngineResult<L, NestedWordAutomaton<L, IPredicate>> refinementResult =
				new TraceAbstractionRefinementEngine<>(checkServices, mLogger, strategy).getResult();

		final LBool feasibility = refinementResult.getCounterexampleFeasibility();
		if (feasibility != LBool.SAT) {
			// The concrete execution and the trace check disagree; one of the two is wrong, and only the trace check
			// may decide. Keep searching.
			mLogger.warn("Value analysis: the trace check answered %s for a run the concrete execution reached an "
					+ "error location with; the run is dropped. Run: %s", feasibility, run.getWord());
			return false;
		}
		final IProgramExecution<L, Term> programExecution;
		if (refinementResult.providesIcfgProgramExecution()) {
			programExecution = refinementResult.getIcfgProgramExecution();
		} else {
			programExecution = TraceCheckUtils.computeSomeIcfgProgramExecutionWithoutValues(run.getWord());
		}
		((IcfgProgramExecution<L>) programExecution).setOriginCfgScript(mCfgSmtToolkit.getManagedScript());
		mViolation = programExecution;
		return true;
	}
}
