package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceOrchestrator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.fixpoint.SubsumptionConvergenceCheck;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.IInterferenceMerger;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.InterferenceCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.mergers.InterferenceCollector.ThreadAnalysisInput;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.transformers.IInterferenceTransformer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public class ThreadModularSifaInterpreter implements ISifaInterpreter {

	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final SymbolicTools mTools;
	private final IIcfg<IcfgLocation> mIcfg;
	private final Set<String> mThreadIds;
	private final Collection<IcfgLocation> mLocationsOfInterest;
	private final IDomain mBaseDomain;
	private final IFluid mFluid;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;

	// Interference components
	private final PrimedDefaultIcfgSymbolTable mPrimedSymbolTable;
	private final SubsumptionConvergenceCheck mConvergenceStrategy;
	private final InterferenceOrchestrator mInterferenceAbstraction;

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mTools = tools;
		mIcfg = icfg;
		mLocationsOfInterest = locationsOfInterest;
		mBaseDomain = baseDomain;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
		// Initialize interference components - collect all thread IDs: main thread + all forked procedures
		final Set<String> threadIds = new HashSet<>();
		threadIds.add(icfg.getInitialNodes().iterator().next().getProcedure());
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			threadIds.add(fork.getNameOfForkedProcedure());
		}
		mThreadIds = threadIds;
		mLogger.info("Discovered threads for thread-modular analysis: " + mThreadIds);
		mPrimedSymbolTable = new PrimedDefaultIcfgSymbolTable(icfg.getCfgSmtToolkit().getSymbolTable(), mThreadIds,
				tools.getManagedScript());

		final BasicPredicateFactory primedFactory = new BasicPredicateFactory(services, tools.getManagedScript(),
				mPrimedSymbolTable);
		final TransFormulaToPredicate translator = new TransFormulaToPredicate(services, tools.getManagedScript(),
				primedFactory, mPrimedSymbolTable);
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services,
				tools.getManagedScript(), tools.getFactory(), mPrimedSymbolTable);

		// Create the shared interference abstraction with default pipeline components
		final InterferenceCollector collector = new InterferenceCollector(translator);
		mInterferenceAbstraction = new InterferenceOrchestrator(baseDomain, postcondition, collector,
				IInterferenceTransformer.identity(), IInterferenceMerger.identity(), mLogger);
		mConvergenceStrategy = new SubsumptionConvergenceCheck();
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {

		final Map<IcfgLocation, IPredicate> result = new HashMap<>();
		InterferenceAbstraction previousInterferences = mInterferenceAbstraction.getInterferences();
		final SifaResultPrinter printer = new SifaResultPrinter(mLogger);
		int iteration = 0;

		// Outer fixpoint loop: iterate until interferences stabilize
		while (true) {
			iteration++;
			mLogger.info("=== Outer Fixpoint Iteration %d ===", iteration);
			// Store analysis results for all threads
			final Map<String, ThreadAnalysisInput> analysisResults = new HashMap<>();
			final Map<String, IIcfg<IcfgLocation>> threadIcfgs = new HashMap<>();

			// Analyze each thread
			for (final String threadId : mThreadIds) {
				mLogger.info(String.format("Analyzing thread: %s", threadId));
				// Create ConcurrentDomain for this thread with the shared abstraction
				final ConcurrentDomain concurrentDomain = new ConcurrentDomain(mBaseDomain, mInterferenceAbstraction,
						threadId);

				final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
				threadIcfgs.put(threadId, threadIcfg);

				// Get LOIs for this thread. If no LOIs exist, use exit node to ensure traversal for interference
				// collection.
				final Collection<IcfgLocation> threadLois = getLocationsOfInterestForThread(threadId);

				final IcfgInterpreter interpreter = new IcfgInterpreter(mLogger, mTimer, mStats, mTools, threadIcfg,
						threadLois, concurrentDomain, mFluid, mLoopSumFactory, mCallSumFactory);
				final Map<IcfgLocation, IPredicate> threadResult = interpreter.interpret();
				result.putAll(threadResult);

				// Store analysis result for interference collection
				analysisResults.put(threadId, new ThreadAnalysisInput(threadResult, threadIcfg));
			}

			// Update interferences via the abstraction (runs collect -> transform -> merge pipeline)
			mInterferenceAbstraction.updateInterferences(analysisResults);
			final InterferenceAbstraction newInterferences = mInterferenceAbstraction.getInterferences();

			// Check fixpoint: are new interferences subsumed by old ones?
			if (mConvergenceStrategy.hasConverged(newInterferences, previousInterferences, mBaseDomain)) {
				mLogger.info("=== Fixpoint reached after %d iterations ===", iteration);
				break;
			}
			previousInterferences = newInterferences;
		}

		// Print final results
//		if (mLogger.isDebugEnabled()) {
		if (true) {
			printer.printResults(result);
		}

		return result;
	}

	/**
	 * Gets locations of interest for a specific thread. If the thread contains LOIs from the global set, those are
	 * returned. Otherwise, the thread's exit node is used as a LOI to ensure the thread is fully traversed for
	 * interference collection.
	 */
	private Collection<IcfgLocation> getLocationsOfInterestForThread(final String threadId) {
		// Filter global LOIs to those in this thread's procedure
		final Collection<IcfgLocation> threadLois = mLocationsOfInterest.stream()
				.filter(loc -> threadId.equals(loc.getProcedure())).toList();

		if (!threadLois.isEmpty()) {
			return threadLois;
		}

		// No LOIs in this thread - use exit node to ensure full traversal for interference collection
		final IcfgLocation exitNode = mIcfg.getProcedureExitNodes().get(threadId);
		if (exitNode != null) {
			mLogger.debug("Thread %s has no LOIs, using exit node for traversal", threadId);
			return Set.of(exitNode);
		}

		// Fallback: use entry node
		final IcfgLocation entryNode = mIcfg.getProcedureEntryNodes().get(threadId);
		if (entryNode != null) {
			mLogger.debug("Thread %s has no LOIs or exit node, using entry node", threadId);
			return Set.of(entryNode);
		}

		mLogger.warn("Thread %s has no entry or exit nodes", threadId);
		return Set.of();
	}
}
