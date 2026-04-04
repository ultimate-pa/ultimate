package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.Collection;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
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
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GuardedPredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceUtils;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators.GuardedOverwriteInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators.PostStateInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators.PrePostInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.applicators.RelationalQeInterferenceApplicator;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.PerAbstractLocationInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.PerEdgeInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.PerThreadInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.factories.PredicateWithSrcAndTrgt;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceMergeDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.LocationTrackingMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.OctagonDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtUtils;
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
		final ILogger logger = services.getLoggingService().getLogger(InterferenceEdgeCollector.class);
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
		final IDomain mergeDomain = createMergeDomainOrNull(settings, tools, services);
		final boolean usePrecomputedGuardedPredicates =
				settings.interferenceApplicatorType() == InterferenceApplicatorType.GUARDED_EXACT_UPDATE;
		final InterferenceEdgeCollector edgeCollector = new InterferenceEdgeCollector(translator, analysisDomain,
				mergeDomain, script, factory, usePrecomputedGuardedPredicates);
		if (mergeDomain != null) {
			logger.info("Interference merge domain: %s", mergeDomain.getClass().getSimpleName());
		}
		final IInterferenceApplicator applicator =
				createApplicator(settings.interferenceApplicatorType(), postcondition, factory, script);
		logger.info("Interference applicator: %s (%s)",
				settings.interferenceApplicatorType(), applicator.getClass().getSimpleName());
		final Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> converter =
				createPredicateConverter(settings.interferenceApplicatorType(), postcondition, factory, script);
		final IInterferenceFactory interferenceFactory = switch (settings.interferenceType()) {
		case PER_THREAD -> new PerThreadInterferenceFactory(edgeCollector, applicator, converter);
		case PER_EDGE -> new PerEdgeInterferenceFactory(edgeCollector, applicator, converter);
		case PER_ABSTRACT_LOCATION -> new PerAbstractLocationInterferenceFactory(edgeCollector, applicator, converter);
		};

		final boolean includeInterferencePreState = true;
		final ThreadModularProofChecker proofChecker = new ThreadModularProofChecker(postcondition, translator,
				analysisDomain, ghostVars, activityPreanalysis,
				activityPreanalysis.getMultiForkedThreads(), includeInterferencePreState);

		return new SetupResult(threadIds, analysisDomain, defaultLoopSumFactory, interferenceFactory, postcondition,
				proofChecker, joinedThreads);
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
		if (workerThreads.size() != 2) {
			return Map.of();
		}
		if (!hasDirectMainTwoWorkerShape(workerThreads, icfg)) {
			return Map.of();
		}
		final Map<String, Set<Integer>> rawIdsByThread = collectRawLocationIdsByThread(locationIds);
		final String firstWorker = workerThreads.get(0);
		final String secondWorker = workerThreads.get(1);
		final Map<String, GuardBucketPolicy> policies = new LinkedHashMap<>();

		final GuardBucketPolicy firstPolicy =
				createGuardBucketPolicy(secondWorker, rawIdsByThread.get(secondWorker), ghostVars, icfg);
		if (firstPolicy != null) {
			policies.put(firstWorker, firstPolicy);
		}

		final GuardBucketPolicy secondPolicy =
				createGuardBucketPolicy(firstWorker, rawIdsByThread.get(firstWorker), ghostVars, icfg);
		if (secondPolicy != null) {
			policies.put(secondWorker, secondPolicy);
		}
		return policies;
	}

	private static boolean hasDirectMainTwoWorkerShape(final List<String> workerThreads, final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> directForkTargets = collectDirectForkTargets(icfg);
		final Set<String> mainForkTargets = directForkTargets.getOrDefault(MAIN_THREAD, Set.of());
		if (mainForkTargets.size() != workerThreads.size() || !mainForkTargets.containsAll(workerThreads)) {
			return false;
		}
		for (final String workerThread : workerThreads) {
			if (!directForkTargets.getOrDefault(workerThread, Set.of()).isEmpty()) {
				return false;
			}
		}
		return true;
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
		final Map<String, Set<String>> forksByThread = new HashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			final String forkingThread = fork.getSource().getProcedure();
			final String forkedThread = fork.getNameOfForkedProcedure();
			forksByThread.computeIfAbsent(forkingThread, k -> new LinkedHashSet<>()).add(forkedThread);
		}
		final List<String> ordered = new ArrayList<>();
		final Set<String> visited = new LinkedHashSet<>();
		ordered.add(MAIN_THREAD);
		visited.add(MAIN_THREAD);
		for (int i = 0; i < ordered.size(); i++) {
			final String current = ordered.get(i);
			final Set<String> forked = forksByThread.get(current);
			if (forked != null) {
				for (final String child : forked) {
					if (visited.add(child)) {
						ordered.add(child);
					}
				}
			}
		}
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			if (visited.add(fork.getNameOfForkedProcedure())) {
				ordered.add(fork.getNameOfForkedProcedure());
			}
		}
		return ordered;
	}

	private static Set<String> identifyJoinedThreads(final IIcfg<IcfgLocation> icfg) {
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final var forks = concurrency.getThreadInstanceMap().keySet();
		final var joins = concurrency.getJoinTransitions();
		final Set<String> joined = new HashSet<>();
		for (final var join : joins) {
			final var joinIdTerms = join.getJoinSmtArguments().getThreadIdArguments().terms();
			for (final var fork : forks) {
				final var forkIdTerms = fork.getForkSmtArguments().getThreadIdArguments().terms();
				if (Arrays.equals(forkIdTerms, joinIdTerms)) {
					joined.add(fork.getNameOfForkedProcedure());
				}
			}
		}
		return joined;
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg, final Set<String> joinedThreads) {
		if (settings.locationTrackingMode() == LocationTrackingMode.NONE) {
			return Map.of();
		}
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
			int maxId = 0;
			boolean exitInMap = locationIds.containsKey(exit);
			boolean shared = false;
			for (final var entry : locationIds.entrySet()) {
				if (threadId.equals(entry.getKey().getProcedure())) {
					maxId = Math.max(maxId, entry.getValue());
					if (entry.getKey() != exit && exitInMap && entry.getValue() == locationIds.get(exit)) {
						shared = true;
					}
				}
			}
			if (!exitInMap || shared) {
				final int freshId = maxId + 1;
				logger.info("Join precision: thread %s exit gets fresh abstract location %d (was %s)",
						threadId, freshId, exitInMap ? locationIds.get(exit) : "absent");
				locationIds.put(exit, freshId);
			}
		}
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

	private static IDomain createMergeDomainOrNull(final ThreadModularSifaSettings settings,
			final SymbolicTools tools, final IUltimateServiceProvider services) {
		if (settings.interferenceMergeDomain() == InterferenceMergeDomain.SAME_AS_ANALYSIS) {
			return null;
		}
		final ILogger logger = services.getLoggingService().getLogger(ThreadModularSetup.class);
		final IProgressAwareTimer neverExpires = new IProgressAwareTimer() {
			@Override
			public boolean continueProcessing() {
				return true;
			}

			@Override
			public IProgressAwareTimer getChildTimer(final long timeout) {
				return this;
			}

			@Override
			public IProgressAwareTimer getChildTimer(final double percentage) {
				return this;
			}

			@Override
			public IProgressAwareTimer getTimer(final long timeout) {
				return this;
			}

			@Override
			public IProgressAwareTimer getParent() {
				return null;
			}

			@Override
			public long getDeadline() {
				return -1;
			}

			@Override
			public long remainingTime() {
				return -1;
			}
		};
		return switch (settings.interferenceMergeDomain()) {
		case OCTAGON -> new OctagonDomain(logger, tools, 2, () -> neverExpires);
		default -> throw new IllegalArgumentException("Unknown merge domain: " + settings.interferenceMergeDomain());
		};
	}

	private static IInterferenceApplicator createApplicator(final InterferenceApplicatorType applicatorType,
			final RelationalPredicatePostcondition postcondition, final BasicPredicateFactory factory,
			final ManagedScript script) {
		return switch (applicatorType) {
		case QE -> new RelationalQeInterferenceApplicator(postcondition);
		case PREPOST -> new PrePostInterferenceApplicator(script, factory);
		case GUARDED_OVERWRITE -> new GuardedOverwriteInterferenceApplicator(script, factory);
		case GUARDED_EXACT_UPDATE -> new GuardedOverwriteInterferenceApplicator(script, factory);
		case POST_STATE -> new PostStateInterferenceApplicator();
		};
	}

	private static Function<PredicateWithSrcAndTrgt, Collection<GuardedPredicate>> createPredicateConverter(
			final InterferenceApplicatorType applicatorType, final RelationalPredicatePostcondition postcondition,
			final BasicPredicateFactory factory, final ManagedScript script) {
		final IPredicate truePredicate = factory.newPredicate(script.getScript().term("true"));
		return switch (applicatorType) {
		case QE -> edgePred -> List.of(GuardedPredicate.unguarded(edgePred.predicate()));
		case POST_STATE -> edgePred -> {
			final var prepared = postcondition.prepareRelation(edgePred.predicate());
			final IPredicate effect = postcondition.strongestPostcondition(truePredicate, prepared);
			return List.of(GuardedPredicate.unguarded(effect));
		};
		case GUARDED_OVERWRITE -> edgePred -> List
				.of(createPreparedGuardedPredicate(edgePred, postcondition, truePredicate, factory, script));
		case GUARDED_EXACT_UPDATE -> edgePred -> List.of(edgePred.precomputedGuardedPredicate() != null
				? edgePred.precomputedGuardedPredicate()
				: createPreparedGuardedPredicate(edgePred, postcondition, truePredicate, factory, script));
		case PREPOST -> edgePred -> {
			final var prepared = postcondition.prepareRelation(edgePred.predicate());
			final List<GuardedPredicate> pairs = new ArrayList<>();
			for (final Term preDisjunctTerm : SmtUtils.getDisjuncts(edgePred.preStateGuard().getFormula())) {
				if (SmtUtils.isFalseLiteral(preDisjunctTerm)) {
					continue;
				}
				final IPredicate preDisjunct = factory.newPredicate(preDisjunctTerm);
				final IPredicate postState = postcondition.strongestPostcondition(preDisjunct, prepared);
				if (!SmtUtils.isFalseLiteral(postState.getFormula())) {
					pairs.add(new GuardedPredicate(preDisjunct, postState));
				}
			}
			return pairs;
		};
		};
	}

	private static GuardedPredicate createPreparedGuardedPredicate(final PredicateWithSrcAndTrgt edgePred,
			final RelationalPredicatePostcondition postcondition, final IPredicate truePredicate,
			final BasicPredicateFactory factory, final ManagedScript script) {
		final var prepared = postcondition.prepareRelation(edgePred.predicate());
		final IPredicate effect = postcondition.strongestPostcondition(truePredicate, prepared);
		final IPredicate guard =
				extractTransitionAwareGuard(edgePred.predicate(), prepared.primedToUnprimed().keySet(), script, factory);
		return new GuardedPredicate(guard, effect, edgePred.modifiedGlobals());
	}

	private static IPredicate extractTransitionAwareGuard(final IPredicate fullRelation,
			final Set<? extends Term> primedVars, final ManagedScript script, final BasicPredicateFactory factory) {
		final Term formula = fullRelation.getFormula();
		final Term[] conjuncts = SmtUtils.getConjuncts(formula);
		final List<Term> preOnly = new ArrayList<>();
		for (final Term conjunct : conjuncts) {
			boolean hasPrimed = false;
			for (final TermVariable fv : conjunct.getFreeVars()) {
				if (primedVars.contains(fv)) {
					hasPrimed = true;
					break;
				}
			}
			if (!hasPrimed) {
				preOnly.add(conjunct);
			}
		}
		if (preOnly.isEmpty()) {
			return null;
		}
		final Term guard = preOnly.size() == 1 ? preOnly.get(0)
				: SmtUtils.and(script.getScript(), preOnly.toArray(new Term[0]));
		return factory.newPredicate(guard);
	}

	public static record SetupResult(List<String> threadIds, IDomain analysisDomain,
			Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			IInterferenceFactory interferenceFactory, RelationalPredicatePostcondition postcondition,
			ThreadModularProofChecker proofChecker, Set<String> joinedThreads) {
	}
}
