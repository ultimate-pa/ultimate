package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.Collection;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.GuardSplitBucketDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.GuardSplitBucketDomain.GuardBucketPolicy;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate.GuardedUpdateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate.PostStateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost.PrePostInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public final class ThreadModularSetup {
	private static final String MAIN_THREAD = "ULTIMATE.start";

	private ThreadModularSetup() {
	}

	public static SetupResult initialize(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final IDomain baseDomain, final IFluid fluid, final SymbolicTools tools,
			final ConcurrentSymbolicTools concurrentTools,
			final Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> defaultLoopSumFactory) {
		final ThreadModularSifaSettings settings = concurrentTools.getSettings();
		final PrimedDefaultIcfgSymbolTable symbolTable = (PrimedDefaultIcfgSymbolTable) tools.getSymbolTable();
		final var factory = tools.getFactory();
		final ManagedScript script = tools.getManagedScript();
		final ILogger logger = services.getLoggingService().getLogger(ThreadModularSetup.class);
		final List<String> threadIds = discoverThreadIds(icfg);
		final Set<String> joinedThreads = settings.joinPrecision() ? identifyJoinedThreads(icfg) : Set.of();
		logger.info("Join precision: %s, joined threads: %s", settings.joinPrecision(), joinedThreads);
		final Map<IcfgLocation, Integer> locationIds = computeLocationIds(settings, services, icfg, joinedThreads);
		final ThreadActivityPreanalysis activityPreanalysis = ThreadActivityPreanalysis.compute(icfg,
				new LinkedHashSet<>(threadIds));

		final GhostVariableManager ghostVars = createGhostVariablesIfEnabled(settings, script, symbolTable, threadIds,
				icfg, locationIds, activityPreanalysis.getMultiForkedThreads());
		concurrentTools.configureStaticAnalysis(ghostVars, activityPreanalysis);
		final Map<String, GuardBucketPolicy> guardBucketPolicies =
				computeEnabledGuardBucketPolicies(logger, settings, ghostVars, threadIds, locationIds, icfg);
		final IDomain analysisDomain = createGuardSplitDomain(baseDomain, tools, guardBucketPolicies);
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable,
				ghostVars, locationIds, icfg.getProcedureEntryNodes());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services, script,
				factory, symbolTable, true);

		final InterferenceEdgeTraverser edgeTraverser = new InterferenceEdgeTraverser(icfg, translator);
		final IInterferenceFactory interferenceFactory = createInterferenceFactory(settings.interferenceApplicatorType(),
				edgeTraverser, translator, postcondition, analysisDomain, factory, script);
		logger.info("Interference method: %s (%s)", settings.interferenceApplicatorType(),
				interferenceFactory.getClass().getSimpleName());
		logger.info("Interference grouping: abstract-location pairs via %s", settings.locationAbstractionType());

		final boolean includeInterferencePreState = true;
		final ThreadModularProofChecker proofChecker = settings.proofCheck()
				? new ThreadModularProofChecker(postcondition, translator, analysisDomain, ghostVars, activityPreanalysis,
						activityPreanalysis.getMultiForkedThreads(), includeInterferencePreState)
				: null;

		return new SetupResult(threadIds, analysisDomain, defaultLoopSumFactory, interferenceFactory, postcondition,
				proofChecker, joinedThreads, locationIds);
	}

	private static Map<String, GuardBucketPolicy> computeEnabledGuardBucketPolicies(final ILogger logger,
			final ThreadModularSifaSettings settings, final GhostVariableManager ghostVars,
			final List<String> threadIds, final Map<IcfgLocation, Integer> locationIds, final IIcfg<IcfgLocation> icfg) {
		if (!settings.guardBucketSplit()) {
			logger.info("Guard bucket split disabled by settings");
			return Map.of();
		}
		if (ghostVars == null || locationIds.isEmpty()) {
			return Map.of();
		}
		final Map<String, GuardBucketPolicy> policies = computeGuardBucketPolicies(threadIds, locationIds, ghostVars, icfg);
		if (policies.isEmpty()) {
			logger.info("Guard bucket split disabled");
			return Map.of();
		}
		for (final var entry : policies.entrySet()) {
			logger.info("Guard bucket split: thread %s bucketed by %s with buckets %s", entry.getKey(),
					entry.getValue().peerThreadId(), entry.getValue().bucketToRawValues());
		}
		return policies;
	}

	private static IDomain createGuardSplitDomain(final IDomain baseDomain, final SymbolicTools tools,
			final Map<String, GuardBucketPolicy> policies) {
		if (policies.isEmpty()) {
			return baseDomain;
		}
		return new GuardSplitBucketDomain(tools, baseDomain, policies);
	}

	private static Map<String, GuardBucketPolicy> computeGuardBucketPolicies(final List<String> threadIds,
			final Map<IcfgLocation, Integer> locationIds, final GhostVariableManager ghostVars,
			final IIcfg<IcfgLocation> icfg) {
		final List<String> workerThreads = threadIds.stream().filter(t -> !MAIN_THREAD.equals(t)).sorted().toList();
		if (workerThreads.size() != 2 || !hasDirectMainTwoWorkerShape(workerThreads, icfg)) {
			return Map.of();
		}
		final Map<String, Set<Integer>> rawIdsByThread = collectRawLocationIdsByThread(locationIds);
		final String firstWorker = workerThreads.get(0);
		final String secondWorker = workerThreads.get(1);
		final Map<String, GuardBucketPolicy> policies = new LinkedHashMap<>();
		putPolicyIfPresent(policies, firstWorker, createGuardBucketPolicy(secondWorker, rawIdsByThread.get(secondWorker),
				ghostVars, icfg));
		putPolicyIfPresent(policies, secondWorker, createGuardBucketPolicy(firstWorker, rawIdsByThread.get(firstWorker),
				ghostVars, icfg));
		return policies;
	}

	private static void putPolicyIfPresent(final Map<String, GuardBucketPolicy> policies, final String threadId,
			final GuardBucketPolicy policy) {
		if (policy != null) {
			policies.put(threadId, policy);
		}
	}

	private static boolean hasDirectMainTwoWorkerShape(final List<String> workerThreads, final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> directForkTargets = collectDirectForkTargets(icfg);
		final Set<String> mainForkTargets = directForkTargets.getOrDefault(MAIN_THREAD, Set.of());
		return mainForkTargets.size() == workerThreads.size() && mainForkTargets.containsAll(workerThreads)
				&& workerThreads.stream().allMatch(workerThread -> directForkTargets.getOrDefault(workerThread, Set.of()).isEmpty());
	}

	private static Map<String, Set<String>> collectDirectForkTargets(final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> forkTargetsByThread = new LinkedHashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			forkTargetsByThread.computeIfAbsent(fork.getSource().getProcedure(), __ -> new LinkedHashSet<>())
					.add(fork.getNameOfForkedProcedure());
		}
		return forkTargetsByThread;
	}

	private static Map<String, Set<Integer>> collectRawLocationIdsByThread(final Map<IcfgLocation, Integer> locationIds) {
		final Map<String, Set<Integer>> idsByThread = new LinkedHashMap<>();
		for (final var entry : locationIds.entrySet()) {
			idsByThread.computeIfAbsent(entry.getKey().getProcedure(), __ -> new LinkedHashSet<>()).add(entry.getValue());
		}
		return idsByThread;
	}

	private static GuardBucketPolicy createGuardBucketPolicy(final String peerThreadId, final Set<Integer> rawIds,
			final GhostVariableManager ghostVars, final IIcfg<IcfgLocation> icfg) {
		if (rawIds == null || rawIds.isEmpty()) {
			return null;
		}
		final TermVariable bucketVariable = ghostVars.getLocationTermVar(peerThreadId);
		if (bucketVariable == null) {
			return null;
		}
		final Integer entryId = ghostVars.getAbstractLocationIdOrNull(ghostVars.getEntryLocation(peerThreadId));
		final IcfgLocation exitLocation = icfg.getProcedureExitNodes().get(peerThreadId);
		final Integer exitId = exitLocation == null ? null : ghostVars.getAbstractLocationIdOrNull(exitLocation);
		final Map<Integer, Integer> rawToBucket = computeRawToBucketMap(rawIds, entryId, exitId);
		if (rawToBucket == null) {
			return null;
		}
		final Map<Integer, Set<Integer>> bucketToRawValues = new LinkedHashMap<>();
		for (final var entry : rawToBucket.entrySet()) {
			bucketToRawValues.computeIfAbsent(entry.getValue(), __ -> new LinkedHashSet<>()).add(entry.getKey());
		}
		if (bucketToRawValues.size() <= 1) {
			return null;
		}
		return new GuardBucketPolicy(peerThreadId, bucketVariable, rawToBucket, bucketToRawValues);
	}

	private static Map<Integer, Integer> computeRawToBucketMap(final Set<Integer> rawIds, final Integer entryId,
			final Integer exitId) {
		final List<Integer> orderedIds = rawIds.stream().sorted().toList();
		final Map<Integer, Integer> rawToBucket = new LinkedHashMap<>();
		for (final Integer rawId : orderedIds) {
			rawToBucket.put(rawId, rawId);
		}
		if (orderedIds.size() > 3) {
			if (orderedIds.size() != 4 || exitId == null || !rawToBucket.containsKey(exitId)) {
				return null;
			}
			final Integer collapsedExitBucket = chooseCollapsedExitBucket(orderedIds, entryId, exitId);
			if (collapsedExitBucket == null) {
				return null;
			}
			rawToBucket.put(exitId, collapsedExitBucket);
		}
		if (entryId != null && rawToBucket.containsKey(entryId)) {
			rawToBucket.put(-1, rawToBucket.get(entryId));
		}
		if (new HashSet<>(rawToBucket.values()).size() > 3) {
			return null;
		}
		return rawToBucket;
	}

	private static Integer chooseCollapsedExitBucket(final List<Integer> orderedIds, final Integer entryId,
			final Integer exitId) {
		Integer candidate = null;
		for (final Integer rawId : orderedIds) {
			if (rawId.equals(exitId)) {
				continue;
			}
			if (entryId != null && rawId.equals(entryId)) {
				continue;
			}
			candidate = rawId;
		}
		if (candidate != null) {
			return candidate;
		}
		for (final Integer rawId : orderedIds) {
			if (!rawId.equals(exitId)) {
				return rawId;
			}
		}
		return null;
	}

	private static List<String> discoverThreadIds(final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> forksByThread = collectDirectForkTargets(icfg);
		final List<String> ordered = new ArrayList<>();
		final Set<String> visited = new LinkedHashSet<>();
		ordered.add(MAIN_THREAD);
		visited.add(MAIN_THREAD);
		appendReachableThreads(ordered, visited, forksByThread);
		icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet().stream()
				.map(fork -> fork.getNameOfForkedProcedure()).filter(visited::add).forEach(ordered::add);
		return ordered;
	}

	private static void appendReachableThreads(final List<String> ordered, final Set<String> visited,
			final Map<String, Set<String>> forksByThread) {
		for (int i = 0; i < ordered.size(); i++) {
			for (final String child : forksByThread.getOrDefault(ordered.get(i), Set.of())) {
				if (visited.add(child)) {
					ordered.add(child);
				}
			}
		}
	}

	private static Set<String> identifyJoinedThreads(final IIcfg<IcfgLocation> icfg) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<List<Term>, String> threadByForkId = concurrency.getThreadInstanceMap().keySet().stream()
				.collect(Collectors.toMap(fork -> List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()),
						fork -> fork.getNameOfForkedProcedure(), (left, right) -> left, LinkedHashMap::new));
		return concurrency.getJoinTransitions().stream()
				.map(join -> threadByForkId.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms())))
				.filter(java.util.Objects::nonNull).collect(Collectors.toSet());
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg, final Set<String> joinedThreads) {
		final var locationAbstraction = new LocationAbstraction<>();
		final Map<IcfgLocation, Integer> ids = new HashMap<>(locationAbstraction
				.computeLocationAbstraction(settings.locationAbstractionType(), services, icfg).toMap());
		if (!joinedThreads.isEmpty()) {
			final ILogger logger = services.getLoggingService().getLogger(ThreadModularSetup.class);
			separateExitLocations(ids, joinedThreads, icfg, logger);
		}
		return ids;
	}

	private static void separateExitLocations(final Map<IcfgLocation, Integer> locationIds,
			final Set<String> joinedThreads, final IIcfg<IcfgLocation> icfg, final ILogger logger) {
		for (final String threadId : joinedThreads) {
			final IcfgLocation exit = icfg.getProcedureExitNodes().get(threadId);
			if (exit == null) {
				continue;
			}
			final boolean exitInMap = locationIds.containsKey(exit);
			final int maxId = maxLocationIdForThread(locationIds, threadId);
			final boolean shared = exitInMap && sharesAbstractLocationWithOtherLocation(locationIds, threadId, exit);
			if (!exitInMap || shared) {
				final int freshId = maxId + 1;
				logger.info("Join precision: thread %s exit gets fresh abstract location %d (was %s)",
						threadId, freshId, exitInMap ? locationIds.get(exit) : "absent");
				locationIds.put(exit, freshId);
			}
		}
	}

	private static int maxLocationIdForThread(final Map<IcfgLocation, Integer> locationIds, final String threadId) {
		return locationIds.entrySet().stream().filter(entry -> threadId.equals(entry.getKey().getProcedure()))
				.mapToInt(Map.Entry::getValue).max().orElse(0);
	}

	private static boolean sharesAbstractLocationWithOtherLocation(final Map<IcfgLocation, Integer> locationIds,
			final String threadId, final IcfgLocation exit) {
		final Integer exitId = locationIds.get(exit);
		return locationIds.entrySet().stream().anyMatch(entry -> threadId.equals(entry.getKey().getProcedure())
				&& entry.getKey() != exit && entry.getValue().equals(exitId));
	}

	private static GhostVariableManager createGhostVariablesIfEnabled(final ThreadModularSifaSettings settings,
			final ManagedScript script, final PrimedDefaultIcfgSymbolTable symbolTable, final List<String> threadIds,
			final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, Integer> locationIds,
			final Set<String> impreciseLocationThreads) {
		if (!settings.useGhostLocations()) {
			return null;
		}
		return GhostVariableManager.create(script, locationIds, new LinkedHashSet<>(threadIds),
				icfg.getProcedureEntryNodes(), symbolTable, impreciseLocationThreads, true);
	}

	private static IInterferenceFactory createInterferenceFactory(final InterferenceApplicatorType applicatorType,
			final InterferenceEdgeTraverser edgeTraverser, final TransFormulaToInterferencePredicate translator,
			final RelationalPredicatePostcondition postcondition, final IDomain analysisDomain,
			final BasicPredicateFactory factory, final ManagedScript script) {
		return switch (applicatorType) {
		case STRONGEST_POSTCONDITION ->
			new StrongestPostconditionInterferenceFactory(edgeTraverser, translator, postcondition, factory, script);
		case PREPOST ->
			new PrePostInterferenceFactory(edgeTraverser, translator, postcondition, script, factory);
		case GUARDED_EXACT_UPDATE ->
			new GuardedUpdateInterferenceFactory(edgeTraverser, translator, postcondition, script, factory);
		case POST_STATE ->
			new PostStateInterferenceFactory(edgeTraverser, translator, postcondition, analysisDomain, factory, script);
		};
	}

	public static record SetupResult(List<String> threadIds, IDomain analysisDomain,
			Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			IInterferenceFactory interferenceFactory, RelationalPredicatePostcondition postcondition,
			ThreadModularProofChecker proofChecker, Set<String> joinedThreads,
			Map<IcfgLocation, Integer> abstractLocationIds) {
	}
}
