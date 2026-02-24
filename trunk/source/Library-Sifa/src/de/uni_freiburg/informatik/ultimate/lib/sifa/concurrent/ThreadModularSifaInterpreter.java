package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceCollection;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFactory;
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

	private final Set<String> mThreadIds;
	private final InterferenceFactory mInterferenceFactory;
	private final IInterference mInterferenceAbstraction;
	private final LoiExpansion mLoiExpansion;
	private final SifaResultPrinter mResultPrinter;
	private final ThreadModularProofChecker mProofChecker;
	private final RelationalPredicatePostcondition mPostcondition;

	private final ConcurrentSymbolicTools mConcurrentTools;
	private final int mOuterWideningThreshold;

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
		mAnalysisDomain = setup.analysisDomain();
		mLoopSumFactory = setup.loopSumFactory();
		mInterferenceFactory = setup.interferenceFactory();
		mInterferenceAbstraction = setup.interferenceBuilder();
		mPostcondition = setup.postcondition();
		mProofChecker = setup.proofChecker();
		mThreadIcfgs = new HashMap<>();
		mThreadLois = new HashMap<>();
		mThreadInterpreters = new HashMap<>();
		prepareThreadIcfgsAndLois();
		final var ghostVars = mConcurrentTools.getGhostVariables();
		final var absLocIds = ghostVars != null ? ghostVars.getAbstractLocationIds() : Map.<IcfgLocation, Integer>of();
		mResultPrinter = new SifaResultPrinter(logger, absLocIds, mConcurrentTools.getThreadActivityPreanalysis());
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final FixpointResult fixpoint = computeOuterInterferenceFixpoint();
		verifyProof(fixpoint);
		mResultPrinter.printResults(fixpoint.locationPredicates, mIcfg);
		return fixpoint.locationPredicates;
	}

	private static record FixpointResult(Map<IcfgLocation, IPredicate> locationPredicates,
			Map<String, Map<IcfgLocation, IPredicate>> threadPredicates) {
	}

	private FixpointResult computeOuterInterferenceFixpoint() {
		final Map<IcfgLocation, IPredicate> allPredicates = new HashMap<>();
		InterferenceCollection currentInterferences = InterferenceCollection.empty();

		for (int iteration = 1;; iteration++) {
			logOuterFixpointIteration(iteration);
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = new HashMap<>();
			analyzeThreads(currentInterferences, allPredicates, perThreadPredicates);
			final InterferenceCollection extractedInterferences = rebuildInterferences(perThreadPredicates);
			logInterferenceCounts(extractedInterferences);

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
			final IInterference rebuilt = mInterferenceAbstraction.build(threadId, locationStates,
					mInterferenceFactory);
			if (!rebuilt.isTrivial()) {
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
			allPredicates.putAll(observed);
			allPredicates.putAll(threadResult);
			perThreadPredicates.put(threadId, interferenceInput);
		}
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
			final Collection<IcfgLocation> lois = mLoiExpansion.getLocationsOfInterestForThread(threadId, threadIcfg,
					mRequestedLocationsOfInterest);
			mThreadLois.put(threadId, List.copyOf(lois));
		}
	}

	private IcfgInterpreter createThreadInterpreter(final String threadId) {
		final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);
		final Collection<IcfgLocation> lois = mThreadLois.get(threadId);
		return new IcfgInterpreter(mLogger, mTimer, mStats, mConcurrentTools, threadIcfg, lois, mAnalysisDomain, mFluid,
				mLoopSumFactory, mCallSumFactory, null);
	}

	private void verifyProof(final FixpointResult fixpoint) {
		if (!mProofChecker.isCheckingEnabled()) {
			mLogger.info("Thread-modular proof checking skipped because ghostvars cant be handled yet");
			return;
		}
		final boolean isValid = mProofChecker.checkAll(mIcfg, fixpoint.locationPredicates, fixpoint.threadPredicates);
		if (!isValid) {
			mLogger.error("Thread-modular proof checking failed");
			throw new IllegalStateException("Thread-modular proof checking failed");
		}
		mLogger.info("Thread-modular proof checking passed");
	}

	private void logOuterFixpointIteration(final int iteration) {
		mLogger.info("Iteration %d", iteration);
	}

	private void logInterferenceCounts(final InterferenceCollection interferences) {
		for (final String threadId : mThreadIds) {
			mLogger.info("  Thread %s: %d interferences", threadId, interferences.getInterferenceCount(threadId));
		}
	}
}
