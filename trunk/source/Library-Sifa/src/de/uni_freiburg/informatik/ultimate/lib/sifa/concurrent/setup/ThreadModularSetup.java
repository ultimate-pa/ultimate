package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.GroupedInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.publish.PublishOnAcquire;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.lockset.MustLocksetAnalysis;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate.GuardedUpdateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate.PostStateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost.PrePostInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals.UnaryGlobalInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.relations.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.InterferenceApplicatorType;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

public final class ThreadModularSetup {
	private static final String MAIN_THREAD = "ULTIMATE.start";

	private ThreadModularSetup() {
	}

	public static SetupResult initialize(final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg,
			final IDomain baseDomain, final SymbolicTools tools, final ConcurrentSymbolicTools concurrentTools) {
		final ThreadModularSifaSettings settings = concurrentTools.getSettings();
		final PrimedDefaultIcfgSymbolTable symbolTable = (PrimedDefaultIcfgSymbolTable) tools.getSymbolTable();
		final var factory = tools.getFactory();
		final ManagedScript script = tools.getManagedScript();
		final ILogger logger = services.getLoggingService().getLogger(ThreadModularSetup.class);
		final List<String> threadIds = discoverThreadIds(icfg);
		final Set<String> joinedThreads = settings.joinPrecision() ? identifyJoinedThreads(icfg) : Set.of();
		if (settings.joinPrecision()) {
			logger.info("Join precision enabled, joined threads: %s", joinedThreads);
		}
		final ThreadActivityPreanalysis activityPreanalysis = ThreadActivityPreanalysis.compute(icfg,
				new LinkedHashSet<>(threadIds), settings.joinPrecision());
		final MustLocksetAnalysis locksetInfo = settings.locksetAwareInterference()
				? MustLocksetAnalysis.create(icfg, activityPreanalysis)
				: MustLocksetAnalysis.disabled();
		final Map<IcfgLocation, Integer> locationIds = computeLocationIds(settings, services, icfg, locksetInfo);
		final Map<String, Set<IcfgLocation>> preForkSourcesByThread =
				computePreForkSourcesByThread(icfg, activityPreanalysis.getMultiForkedThreads());

		final GhostVariableManager ghostVars = createGhostVariablesIfEnabled(settings, script, symbolTable, threadIds,
				icfg, locationIds, activityPreanalysis.getMultiForkedThreads());
		concurrentTools.initializeStaticAnalysis(ghostVars, activityPreanalysis, locksetInfo);
		final PublishOnAcquire lockInvariants = settings.publishOnAcquire()
				? PublishOnAcquire.discoverProtectedGlobalsAndPublishEdgesDuringPreanalysis(icfg, locksetInfo,
						MAIN_THREAD, activityPreanalysis, services, script, factory)
				: PublishOnAcquire.disabled();
		if (settings.publishOnAcquire()) {
			logger.info("Publish-on-acquire enabled (protected globals discovered: %s)", !lockInvariants.isEmpty());
		}
		final boolean hasArrayGlobals = hasArrayTypedGlobals(icfg);
		final AbstractLocationPartitionedDomain partitionedDomain =
				usesLocationPartitioning(settings) && ghostVars != null && !hasArrayGlobals
				? AbstractLocationPartitionedDomain.create(baseDomain, tools,
						ghostVars.getLocationTermVariablesByThread(), settings.maxBuckets(),
						settings.maxDisjunctsPerBucket())
				: null;
		if (partitionedDomain != null) {
			logger.info("Abstract-location partitioned domain enabled");
		} else if (usesLocationPartitioning(settings) && hasArrayGlobals) {
			logger.info("Abstract-location partitioned domain disabled: array-typed shared globals present");
		}
		final IDomain domain = partitionedDomain != null ? partitionedDomain : baseDomain;
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable,
				ghostVars, locationIds, icfg.getProcedureEntryNodes());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services, script,
				factory, symbolTable, true);
		final InterferenceEdgeCollector edgeTraverser = new InterferenceEdgeCollector(icfg, translator);
		final GroupedInterferenceFactory<?> interferenceFactory = createInterferenceFactory(
				settings.interferenceApplicatorType(), edgeTraverser, translator, postcondition, domain, factory,
				script, locksetInfo, preForkSourcesByThread);
		logger.info("Interference method: %s (%s)", settings.interferenceApplicatorType(),
				interferenceFactory == null ? "None" : interferenceFactory.getClass().getSimpleName());
		logger.info("Interference grouping: abstract-location pairs via %s", settings.locationAbstractionType());

		final ThreadModularProofChecker proofChecker = settings.proofCheck()
				? new ThreadModularProofChecker(icfg, postcondition, translator, domain, ghostVars, activityPreanalysis)
				: null;

		return new SetupResult(threadIds, domain, interferenceFactory, postcondition,
				proofChecker, joinedThreads, locationIds, lockInvariants);
	}

	private static boolean usesLocationPartitioning(final ThreadModularSifaSettings settings) {
		if (!settings.useBuckets()) {
			return false;
		}
		final InterferenceApplicatorType type = settings.interferenceApplicatorType();
		return type == InterferenceApplicatorType.STRONGEST_POSTCONDITION;
	}

	private static boolean hasArrayTypedGlobals(final IIcfg<IcfgLocation> icfg) {
		return icfg.getCfgSmtToolkit().getSymbolTable().getGlobals().stream()
				.anyMatch(v -> v.getSort().isArraySort());
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

	private static Map<String, Set<String>> collectDirectForkTargets(final IIcfg<IcfgLocation> icfg) {
		final Map<String, Set<String>> forkTargetsByThread = new LinkedHashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			forkTargetsByThread.computeIfAbsent(fork.getSource().getProcedure(), __ -> new LinkedHashSet<>())
					.add(fork.getNameOfForkedProcedure());
		}
		return forkTargetsByThread;
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
		return Set.copyOf(ThreadActivityPreanalysis.matchJoinsToThreads(icfg, null).values());
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg, final MustLocksetAnalysis locksetInfo) {
		return new LocationAbstraction().computeLocationAbstraction(settings.locationAbstractionType(),
				services, icfg, locksetInfo);
	}

	private static Map<String, Set<IcfgLocation>> computePreForkSourcesByThread(final IIcfg<IcfgLocation> icfg,
			final Set<String> multiForkedThreads) {
		final Map<String, List<IIcfgForkTransitionThreadCurrent<IcfgLocation>>> forksByThread = new LinkedHashMap<>();
		for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork
				: icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			forksByThread.computeIfAbsent(fork.getNameOfForkedProcedure(), ignored -> new ArrayList<>()).add(fork);
		}

		final Map<String, Set<IcfgLocation>> result = new LinkedHashMap<>();
		for (final var entry : forksByThread.entrySet()) {
			if (entry.getValue().size() != 1) {
				continue;
			}
			final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork = entry.getValue().get(0);
			final IcfgLocation forkSource = fork.getSource();
			final IcfgLocation forkTarget = fork.getTarget();
			if (forkSource == null || forkTarget == null) {
				continue;
			}
			if (multiForkedThreads.contains(forkSource.getProcedure())) {
				continue;
			}
			final Set<IcfgLocation> reachableAfterFork = reachableSameProcedure(forkTarget);
			final Set<IcfgLocation> preForkSources = new LinkedHashSet<>();
			for (final IcfgLocation candidate : icfg.getProgramPoints().getOrDefault(forkSource.getProcedure(), Map.of())
					.values()) {
				if (reachableAfterFork.contains(candidate)) {
					continue;
				}
				if (reachableSameProcedure(candidate).contains(forkSource)) {
					preForkSources.add(candidate);
				}
			}
			if (!preForkSources.isEmpty()) {
				result.put(entry.getKey(), Set.copyOf(preForkSources));
			}
		}
		return Map.copyOf(result);
	}

	private static Set<IcfgLocation> reachableSameProcedure(final IcfgLocation start) {
		final Set<IcfgLocation> result = new LinkedHashSet<>();
		final ArrayDeque<IcfgLocation> pending = new ArrayDeque<>();
		result.add(start);
		pending.add(start);
		while (!pending.isEmpty()) {
			final IcfgLocation source = pending.removeFirst();
			for (final IcfgEdge edge : source.getOutgoingEdges()) {
				final IcfgLocation target = edge.getTarget();
				if (target == null || !start.getProcedure().equals(target.getProcedure()) || !result.add(target)) {
					continue;
				}
				pending.add(target);
			}
		}
		return result;
	}

	private static GhostVariableManager createGhostVariablesIfEnabled(final ThreadModularSifaSettings settings,
			final ManagedScript script, final PrimedDefaultIcfgSymbolTable symbolTable, final List<String> threadIds,
			final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, Integer> locationIds,
			final Set<String> impreciseLocationThreads) {
		if (!settings.useGhostLocations()) {
			return null;
		}
		return GhostVariableManager.create(script, locationIds, new LinkedHashSet<>(threadIds),
				icfg.getProcedureEntryNodes(), symbolTable, impreciseLocationThreads);
	}

	private static GroupedInterferenceFactory<?> createInterferenceFactory(final InterferenceApplicatorType applicatorType,
			final InterferenceEdgeCollector edgeTraverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory factory, final ManagedScript script,
			final MustLocksetAnalysis locksetInfo, final Map<String, Set<IcfgLocation>> preForkSourcesByThread) {
		return switch (applicatorType) {
		case STRONGEST_POSTCONDITION ->
			new StrongestPostconditionInterferenceFactory(edgeTraverser, translator, postcondition, factory, script,
					locksetInfo, preForkSourcesByThread);
		case PREPOST ->
			new PrePostInterferenceFactory(edgeTraverser, translator, postcondition, script, factory, locksetInfo,
					preForkSourcesByThread);
		case GUARDED_EXACT_UPDATE ->
			new GuardedUpdateInterferenceFactory(edgeTraverser, translator, postcondition, script, factory,
					locksetInfo, preForkSourcesByThread);
		case POST_STATE ->
			new PostStateInterferenceFactory(edgeTraverser, translator, postcondition, domain, factory, script,
					locksetInfo, preForkSourcesByThread);
		case UNARY_GLOBALS ->
			new UnaryGlobalInterferenceFactory(edgeTraverser, translator.getServices(), translator, postcondition,
					domain, factory, script, locksetInfo);
		case NONE -> null;
		};
	}

	public static record SetupResult(List<String> threadIds, IDomain domain,
			GroupedInterferenceFactory<?> interferenceFactory, RelationalPredicatePostcondition postcondition,
			ThreadModularProofChecker proofChecker, Set<String> joinedThreads,
			Map<IcfgLocation, Integer> abstractLocationIds, PublishOnAcquire lockInvariants) {
	}
}
