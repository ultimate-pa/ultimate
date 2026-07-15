package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.lib.exceptions.ToolchainCanceledException;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.ISifaInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LoiExpansion;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.SingleThreadIcfg;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceSet;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSetup;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats;
import de.uni_freiburg.informatik.ultimate.lib.sifa.statistics.SifaStats.Key;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ICallSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;

public class ThreadModularSifaInterpreter implements ISifaInterpreter {
	private static final int MAX_OUTER_INTERFERENCE_ITERATIONS = 100;
	private static final int PUBLICATION_WIDENING_DELAY = 5;

	private final ILogger mLogger;
	private final IProgressAwareTimer mTimer;
	private final SifaStats mStats;
	private final IIcfg<IcfgLocation> mIcfg;
	private final IDomain mDomain;
	private final IFluid mFluid;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> mLoopSumFactory;
	private final Function<IcfgInterpreter, Function<DagInterpreter, ICallSummarizer>> mCallSumFactory;
	private final Collection<IcfgLocation> mRequestedLocationsOfInterest;
	private final Map<String, IIcfg<IcfgLocation>> mThreadIcfgs;
	private final Map<String, Collection<IcfgLocation>> mThreadLois;
	private final Map<String, IcfgInterpreter> mThreadInterpreters;
	private final Map<String, Set<IcfgLocation>> mForkSourcesByThread;

	private final List<String> mThreadIds;
	private final Set<String> mJoinedThreads;
	private final GroupedInterferenceFactory<?> mInterferenceFactory;
	private final SifaResultPrinter mResultPrinter;
	private final ThreadModularProofChecker mProofChecker;
	private final RelationalPredicatePostcondition mPostcondition;
	private final ConcurrentSymbolicTools mConcurrentTools;
	private final int mOuterWideningThreshold;
	private final PublishOnAcquire mStaticLockInvariants;

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

		mConcurrentTools = (ConcurrentSymbolicTools) tools;
		mOuterWideningThreshold = mConcurrentTools.getSettings().outerWideningThreshold();
		final var setup = ThreadModularSetup.initialize(services, icfg, baseDomain, tools, mConcurrentTools);
		mThreadIds = setup.threadIds();
		mJoinedThreads = setup.joinedThreads();
		mDomain = setup.domain();
		mInterferenceFactory = setup.interferenceFactory();
		mStaticLockInvariants = setup.lockInvariants();
		mPostcondition = setup.postcondition();
		mPostcondition.setStats(mStats);
		mProofChecker = setup.proofChecker();
		mThreadIcfgs = new HashMap<>();
		mThreadLois = new HashMap<>();
		mThreadInterpreters = new HashMap<>();
		mForkSourcesByThread = collectForkSourcesByThread();
		prepareThreadIcfgsAndLois();
		mResultPrinter = mConcurrentTools.getSettings().resultPrint()
				? new SifaResultPrinter(logger, setup.abstractLocationIds(),
						mConcurrentTools.getThreadActivityPreanalysis())
				: null;
	}

	@Override
	public Map<IcfgLocation, IPredicate> interpret() {
		final FixpointResult fixpoint = computeOuterInterferenceFixpoint();
		if (mResultPrinter != null) {
			mResultPrinter.printResults(fixpoint.locationPredicates, mIcfg);
		}
		if (mProofChecker != null) {
			mProofChecker.checkAllOrThrow(fixpoint.locationPredicates, fixpoint.threadPredicates, mLogger);
		}
		return fixpoint.locationPredicates;
	}

	private static record FixpointResult(Map<IcfgLocation, IPredicate> locationPredicates,
			Map<String, Map<IcfgLocation, IPredicate>> threadPredicates) {
	}

	private FixpointResult computeOuterInterferenceFixpoint() {
		final Map<IcfgLocation, IPredicate> allPredicates = new LinkedHashMap<>();
		IInterferenceSet currentInterferences = null;
		PublishOnAcquire currentPublication = mStaticLockInvariants;
		final Set<IcfgLocation> joinedExitLocations = computeJoinedExitLocations();
		boolean rerunWithStableInterferences = false;

		if (mConcurrentTools.getSettings().interferenceApplicatorType() == InterferenceApplicatorType.NONE) {
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = new LinkedHashMap<>();
			mConcurrentTools.setLockInvariants(currentPublication);
			analyzeThreads(null, allPredicates, perThreadPredicates);
			return new FixpointResult(allPredicates, perThreadPredicates);
		}

		for (int iteration = 1;; iteration++) {
			if (!mTimer.continueProcessing()) {
				throw new ToolchainCanceledException(getClass(), "Timeout during outer thread-modular fixpoint");
			}
			if (iteration > MAX_OUTER_INTERFERENCE_ITERATIONS) {
				throw new ToolchainCanceledException(getClass(),
						"Outer thread-modular fixpoint did not converge after "
								+ MAX_OUTER_INTERFERENCE_ITERATIONS + " iterations");
			}
			mLogger.info("Iteration %d", iteration);
			final Map<IcfgLocation, IPredicate> joinedExitsBefore =
					joinedExitLocations.isEmpty() ? Map.of() : snapshotLocations(allPredicates, joinedExitLocations);
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates = new LinkedHashMap<>();
			mConcurrentTools.setLockInvariants(currentPublication);
			analyzeThreads(currentInterferences, allPredicates, perThreadPredicates);
			final IInterferenceSet extractedInterferences =
					mInterferenceFactory.buildFromAllStates(perThreadPredicates);
			if (extractedInterferences != null) {
				mStats.add(Key.INTERFERENCE_SUMMARIES_BUILT, extractedInterferences.summaryCount());
			}
			final PublishOnAcquire extractedPublication =
					mStaticLockInvariants.recomputePublishedInvariants(allPredicates, mDomain,
							mConcurrentTools::postWithoutInterference);
			final boolean interferencesHaveConverged = hasConverged(extractedInterferences, currentInterferences);
			final boolean publicationConverged = extractedPublication.isSubsumedBy(currentPublication, mDomain);

			if (interferencesHaveConverged && publicationConverged) {
				if (rerunWithStableInterferences
						|| joinedExitLocations.isEmpty()
						|| joinedExitPredicatesUnchanged(allPredicates, joinedExitsBefore)) {
					return new FixpointResult(allPredicates, perThreadPredicates);
				}
				rerunWithStableInterferences = true;
				currentPublication = extractedPublication;
				continue;
			}
			rerunWithStableInterferences = false;
			currentPublication = iteration >= mOuterWideningThreshold + PUBLICATION_WIDENING_DELAY
					? currentPublication.widen(extractedPublication, mDomain)
					: extractedPublication;
			if (iteration >= mOuterWideningThreshold) {
				currentInterferences = widen(currentInterferences, extractedInterferences);
				mStats.increment(Key.INTERFERENCE_OUTER_WIDENINGS);
			} else {
				currentInterferences = extractedInterferences;
			}
		}
	}

	private boolean hasConverged(final IInterferenceSet extracted, final IInterferenceSet current) {
		if (extracted == null) {
			return true;
		}
		if (current == null) {
			return false;
		}
		return extracted.isSubsumedBy(current, mDomain);
	}

	private IInterferenceSet widen(final IInterferenceSet current, final IInterferenceSet extracted) {
		if (current == null) {
			return extracted;
		}
		return current.widen(extracted, mDomain);
	}

	private Set<IcfgLocation> computeJoinedExitLocations() {
		final Set<IcfgLocation> exits = new LinkedHashSet<>();
		for (final String threadId : mJoinedThreads) {
			final IcfgLocation exit = mThreadIcfgs.get(threadId).getProcedureExitNodes().get(threadId);
			if (exit != null) {
				exits.add(exit);
			}
		}
		return Set.copyOf(exits);
	}

	private static Map<IcfgLocation, IPredicate> snapshotLocations(final Map<IcfgLocation, IPredicate> allPredicates,
			final Set<IcfgLocation> locations) {
		final Map<IcfgLocation, IPredicate> snapshot = new LinkedHashMap<>(locations.size() * 2);
		for (final IcfgLocation loc : locations) {
			snapshot.put(loc, allPredicates.get(loc));
		}
		return snapshot;
	}

	private boolean joinedExitPredicatesUnchanged(final Map<IcfgLocation, IPredicate> allPredicates,
			final Map<IcfgLocation, IPredicate> snapshot) {
		for (final Map.Entry<IcfgLocation, IPredicate> entry : snapshot.entrySet()) {
			final IPredicate before = entry.getValue();
			final IPredicate after = allPredicates.get(entry.getKey());
			if (before == after) {
				continue;
			}
			if (before == null || after == null) {
				return false;
			}
			if (!mDomain.isSubsetEq(before, after).isTrueForAbstraction()
					|| !mDomain.isSubsetEq(after, before).isTrueForAbstraction()) {
				return false;
			}
		}
		return true;
	}

	private void analyzeThreads(final IInterferenceSet interference,
			final Map<IcfgLocation, IPredicate> allPredicates,
			final Map<String, Map<IcfgLocation, IPredicate>> perThreadPredicates) {
		for (final String threadId : mThreadIds) {
			final IIcfg<IcfgLocation> threadIcfg = mThreadIcfgs.get(threadId);

			mConcurrentTools.configureForThread(threadId, interference, allPredicates, mDomain);
			final IPredicate initialState = mConcurrentTools.getInitialStatePredicate(threadId);
			final IcfgLocation entryLocation = threadIcfg.getProcedureEntryNodes().get(threadId);
			mConcurrentTools.rememberThreadLocationState(entryLocation, initialState);

			final Map<IcfgLocation, IPredicate> threadResult = analyzeSingleThread(threadId, initialState);
			final Map<IcfgLocation, IPredicate> observed = mConcurrentTools.getObservedThreadLocationStates();
			final Map<IcfgLocation, IPredicate> interferenceInput = new LinkedHashMap<>(observed);
			interferenceInput.putAll(threadResult);
			allPredicates.putAll(threadResult);
			for (final var entry : observed.entrySet()) {
				if (!threadResult.containsKey(entry.getKey()) || isForkSourceLocation(entry.getKey())) {
					allPredicates.put(entry.getKey(), entry.getValue());
				}
			}
			perThreadPredicates.put(threadId, interferenceInput);
		}
	}

	private static boolean isForkSourceLocation(final IcfgLocation location) {
		return location.getOutgoingEdges().stream()
				.anyMatch(edge -> edge instanceof IIcfgForkTransitionThreadCurrent<?>);
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
			final Collection<IcfgLocation> baseLois = LoiExpansion.getLocationsOfInterestForThread(threadId,
					threadIcfg, mRequestedLocationsOfInterest);
			final Set<IcfgLocation> expandedLois = new LinkedHashSet<>(baseLois);
			final Set<IcfgLocation> forkSources = mForkSourcesByThread.getOrDefault(threadId, Set.of());
			expandedLois.addAll(forkSources);
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
		final IDomain effDomain = mConcurrentTools.getEffectiveDomain();
		final IDomain interpDomain = effDomain != null ? effDomain : mDomain;
		return new IcfgInterpreter(mLogger, mTimer, mStats, mConcurrentTools, threadIcfg, lois, interpDomain, mFluid,
				mLoopSumFactory, mCallSumFactory, null);
	}

	private Map<String, Set<IcfgLocation>> collectForkSourcesByThread() {
		final Map<String, Set<IcfgLocation>> result = new LinkedHashMap<>();
		for (final var procedurePoints : mIcfg.getProgramPoints().values()) {
			for (final IcfgLocation location : procedurePoints.values()) {
				for (final var edge : location.getOutgoingEdges()) {
					if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
						result.computeIfAbsent(location.getProcedure(), __ -> new LinkedHashSet<>()).add(location);
					}
				}
			}
		}
		return Map.copyOf(result);
	}

}
