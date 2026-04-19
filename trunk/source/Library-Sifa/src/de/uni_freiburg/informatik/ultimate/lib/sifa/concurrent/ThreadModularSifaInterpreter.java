package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSetup;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public class ThreadModularSifaInterpreter implements ISifaInterpreter {

	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IDomain mAnalysisDomain;
	private final IFluid mFluid;
	private Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;
	private final Map<String, IIcfg<IcfgLocation>> mThreadIcfgs;
	private final Map<String, Collection<IcfgLocation>> mThreadLois;
	private final Map<String, IcfgInterpreter> mThreadInterpreters;

	private final List<String> mThreadIds;
	private final Set<String> mJoinedThreads;
	private final IInterferenceFactory mInterferenceFactory;
	private final LoiExpansion mLoiExpansion;
	private final SifaResultPrinter mResultPrinter;
	private final ThreadModularProofChecker mProofChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final boolean mResultPrint;

	private final ConcurrentSymbolicTools mConcurrentTools;
	private final int mOuterWideningThreshold;

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory) {
		this(logger, timer, stats, tools, icfg, locationsOfInterest, baseDomain, fluid, loopSumFactory, callSumFactory,
				extractServices(tools));
	}

	public ThreadModularSifaInterpreter(final ILogger logger, final IProgressAwareTimer timer, final SifaStats stats,
			final SymbolicTools tools, final IIcfg<IcfgLocation> icfg,
			final Collection<IcfgLocation> locationsOfInterest, final IDomain baseDomain, final IFluid fluid,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> callSumFactory,
			final IUltimateServiceProvider services) {
		mLogger = logger;
		mTimer = timer;
		mStats = stats;
		mIcfg = icfg;
		mFluid = fluid;
		mLoopSumFactory = loopSumFactory;
		mCallSumFactory = callSumFactory;
		mRequestedLocationsOfInterest = locationsOfInterest == null ? Set.of() : Set.copyOf(locationsOfInterest);

		mLoiExpansion = new LoiExpansion();
		mConcurrentTools = (ConcurrentSymbolicTools) tools;
		mOuterWideningThreshold = mConcurrentTools.getSettings().outerWideningThreshold();
		final var setup = ThreadModularSetup.initialize(services, icfg, baseDomain, fluid, tools, mConcurrentTools,
				loopSumFactory);
		mThreadIds = setup.threadIds();
		mJoinedThreads = setup.joinedThreads();
		mAnalysisDomain = setup.analysisDomain();
		mLoopSumFactory = setup.loopSumFactory();
		mInterferenceFactory = setup.interferenceFactory();
		mPostcondition = setup.postcondition();
		mPostcondition.setStats(mStats);
		mProofChecker = setup.proofChecker();
		mResultPrint = mConcurrentTools.getSettings().resultPrint();
		mThreadIcfgs = new HashMap<>();
		mThreadLois = new HashMap<>();
		mThreadInterpreters = new HashMap<>();
		prepareThreadIcfgsAndLois();
		mResultPrinter = mResultPrint
				? new SifaResultPrinter(logger, setup.abstractLocationIds(),
						mConcurrentTools.getThreadActivityPreanalysis())
				: null;
	}

	private static IUltimateServiceProvider extractServices(final SymbolicTools tools) {
		if (tools instanceof final ConcurrentSymbolicTools concurrentTools) {
			return concurrentTools.getServices();
		}
		throw new IllegalArgumentException(
				"ThreadModularSifaInterpreter requires ConcurrentSymbolicTools when using the legacy constructor");
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final FixpointResult fixpoint = computeOuterInterferenceFixpoint();
		if (false) {
			if (mResultPrinter != null) {
				mResultPrinter.printResults(fixpoint.locationPredicates, mIcfg);
			} else {
				mLogger.info("Thread-modular result printing disabled");
			}
		}
		if (false) {
			verifyProof(fixpoint);
		}
		return fixpoint.locationPredicates;
	}

	private static record FixpointResult(Map<IcfgLocation, IPredicate> locationPredicates,
			Map<String, Map<IcfgLocation, IPredicate>> threadPredicates) {
	}

	private FixpointResult computeOuterInterferenceFixpoint() {
		final Map<IcfgLocation, IPredicate> allPredicates = new HashMap<>();
		InterferenceCollection currentInterferences = InterferenceCollection.empty();

		for (int iteration = 1;; iteration++) {
			mLogger.info("Iteration %d", iteration);
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = new HashMap<>();
			analyzeThreads(currentInterferences, allPredicates, perThreadPredicates);
			final InterferenceCollection extractedInterferences = rebuildInterferences(perThreadPredicates);

			if (extractedInterferences.hasConverged(currentInterferences, mAnalysisDomain)) {
				return new FixpointResult(allPredicates, perThreadPredicates);
			}
			final InterferenceCollection nextInterferences;
			if (iteration >= mOuterWideningThreshold) {
				nextInterferences = currentInterferences.widen(extractedInterferences, mAnalysisDomain);
				mStats.increment(Key.INTERFERENCE_OUTER_WIDENINGS);
			} else {
				nextInterferences = extractedInterferences;
			}
			currentInterferences = nextInterferences;
		}
	}

	private InterferenceCollection rebuildInterferences(
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates) {
		final Map<String, IInterference> rebuiltInterferences = new HashMap<>();
		for (final String threadId : mThreadIds) {
			final Map<IcfgLocation, IPredicate> locationStates = perThreadPredicates.get(threadId);
			if (locationStates == null) {
				continue;
			}
			final IInterference rebuilt = mInterferenceFactory.buildFromStates(threadId, locationStates);
			if (rebuilt != null) {
				rebuiltInterferences.put(threadId, rebuilt);
			}
		}
		return InterferenceCollection.of(rebuiltInterferences);
	}

	private void analyzeThreads(final InterferenceCollection interferences,
			final Map<IcfgLocation, IPredicate> allPredicates,
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates) {
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);

			mConcurrentTools.configureForThread(threadId, interferences, allPredicates, mAnalysisDomain,
					mAnalysisDomain, mPostcondition);
			final IPredicate initialState = mConcurrentTools.getInitialStatePredicate(threadId);
			final IcfgLocation entryLocation = threadIcfg.getProcedureEntryNodes().get(threadId);
			mConcurrentTools.rememberThreadLocationState(entryLocation, initialState);

			final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, initialState);
			final Map<IcfgLocation, IPredicate> observed = mConcurrentTools.getObservedThreadLocationStates();
			final Map<IcfgLocation, IPredicate> interferenceInput = new HashMap<>(observed);
			interferenceInput.putAll(threadResult);
			allPredicates.putAll(threadResult);
			for (final var entry : observed.entrySet()) {
				if (!allPredicates.containsKey(entry.getKey()) || isForkSourceLocation(entry.getKey())) {
					if (isForkSourceLocation(entry.getKey()) && threadResult.containsKey(entry.getKey())
							&& !threadResult.get(entry.getKey()).getFormula().equals(entry.getValue().getFormula())) {
						mLogger.info("Using observed fork-source state at %s for next thread initialization",
								entry.getKey());
					}
					allPredicates.put(entry.getKey(), entry.getValue());
				}
			}
			perThreadPredicates.put(threadId, interferenceInput);
		}
	}

	private static boolean isForkSourceLocation(final IcfgLocation location) {
		return location.getOutgoingEdges().stream().anyMatch(
				edge -> edge instanceof de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent<?>);
	}

	private Map<IcfgLocation, IPredicate> analyzeSingleThread(final String threadId, final IPredicate initialState) {
		final IcfgInterpreter interpreter = mThreadInterpreters.computeIfAbsent(threadId,
				this::createThreadInterpreter);
		return interpreter.interpret(initialState);
	}

	private void prepareThreadIcfgsAndLois() {
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = new SingleThreadIcfg(mIcfg, threadId);
			mThreadIcfgs.put(threadId, threadIcfg);
			final Collection<IcfgLocation> baseLois = mLoiExpansion.getLocationsOfInterestForThread(threadId,
					threadIcfg, mRequestedLocationsOfInterest);
			final Set<IcfgLocation> expandedLois = new LinkedHashSet<>(baseLois);
			if (mJoinedThreads.contains(threadId)) {
				final IcfgLocation exit = threadIcfg.getProcedureExitNodes().get(threadId);
				if (exit != null) {
					expandedLois.add(exit);
				}
			}
			mThreadLois.put(threadId, List.copyOf(expandedLois));
		}
	}

	private IcfgInterpreter createThreadInterpreter(final String threadId) {
		final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);
		final Collection<IcfgLocation> lois = mThreadLois.get(threadId);
		return new IcfgInterpreter(mLogger, mTimer, mStats, mConcurrentTools, threadIcfg, lois, mAnalysisDomain, mFluid,
				mLoopSumFactory, mCallSumFactory, null);
	}

	private void verifyProof(final FixpointResult fixpoint) {
		if (mProofChecker == null) {
			mLogger.info("Thread-modular proof checking disabled");
			return;
		}
		mProofChecker.checkAllOrThrow(fixpoint.locationPredicates, fixpoint.threadPredicates, mLogger);
	}

}
