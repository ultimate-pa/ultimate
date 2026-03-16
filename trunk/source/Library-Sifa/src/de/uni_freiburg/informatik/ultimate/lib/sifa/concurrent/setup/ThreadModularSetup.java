package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeCollector;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerAbstractLocationInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerEdgeInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.PerThreadInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.PrimedDefaultIcfgSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.RelationalPredicatePostcondition;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.primedFormulas.TransFormulaToInterferencePredicate;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.proofchecking.ThreadModularProofChecker;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup.ThreadModularSifaSettings.LocationTrackingMode;
import de.uni_freiburg.informatik.ultimate.lib.sifa.domain.IDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.fluid.IFluid;
import de.uni_freiburg.informatik.ultimate.lib.sifa.summarizers.ILoopSummarizer;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;

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
		final IDomain analysisDomain = baseDomain;
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable,
				ghostVars, locationIds, icfg.getProcedureEntryNodes());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services, script,
				factory, symbolTable, true);
		final InterferenceEdgeCollector edgeCollector = new InterferenceEdgeCollector(translator, analysisDomain,
				script, factory, logger);
		final IInterferenceFactory interferenceFactory = switch (settings.interferenceType()) {
		case PER_THREAD -> new PerThreadInterferenceFactory(edgeCollector);
		case PER_EDGE -> new PerEdgeInterferenceFactory(edgeCollector);
		case PER_ABSTRACT_LOCATION -> new PerAbstractLocationInterferenceFactory(edgeCollector);
		};

		final boolean includeInterferencePreState = true;
		final ThreadModularProofChecker proofChecker = new ThreadModularProofChecker(icfg.getCfgSmtToolkit(),
				postcondition, translator, analysisDomain, ghostVars, activityPreanalysis,
				activityPreanalysis.getMultiForkedThreads(), includeInterferencePreState);

		return new SetupResult(threadIds, analysisDomain, defaultLoopSumFactory, interferenceFactory, postcondition,
				proofChecker, joinedThreads);
	}

	/** Thread IDs in topological fork order: forking thread before any it forks. */
	private static List<String> discoverThreadIds(final IIcfg<IcfgLocation> icfg) {
		// fork graph: forker -> forked threads
		final Map<String, Set<String>> forksByThread = new HashMap<>();
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			final String forkingThread = fork.getSource().getProcedure();
			final String forkedThread = fork.getNameOfForkedProcedure();
			forksByThread.computeIfAbsent(forkingThread, k -> new LinkedHashSet<>()).add(forkedThread);
		}
		// BFS from MAIN_THREAD gives topological order
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
		// threads not reachable via fork edges (shouldn't happen, but be safe)
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			if (visited.add(fork.getNameOfForkedProcedure())) {
				ordered.add(fork.getNameOfForkedProcedure());
			}
		}
		return ordered;
	}

	/** Match join-current to fork edges via thread ID terms to find joined procedures. */
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
			// Exit node may not be in locationIds if the location abstraction didn't reach it
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

	public static record SetupResult(List<String> threadIds, IDomain analysisDomain,
			Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			IInterferenceFactory interferenceFactory, RelationalPredicatePostcondition postcondition,
			ThreadModularProofChecker proofChecker, Set<String> joinedThreads) {
	}
}
