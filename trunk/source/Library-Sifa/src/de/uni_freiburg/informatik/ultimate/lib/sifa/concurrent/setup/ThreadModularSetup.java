package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.BasicPredicateFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.bucketdomain.AbstractLocationPartitionedDomain;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceEdgeTraverser;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.guardedupdate.GuardedUpdateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.poststate.PostStateInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.prepost.PrePostInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.strongestpostcondition.StrongestPostconditionInterferenceFactory;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.methods.unaryglobals.UnaryGlobalInterferenceFactory;
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
		if (settings.joinPrecision()) {
			logger.info("Join precision enabled, joined threads: %s", joinedThreads);
		}
		final Map<IcfgLocation, Integer> locationIds = computeLocationIds(settings, services, icfg, joinedThreads);
		final ThreadActivityPreanalysis activityPreanalysis = ThreadActivityPreanalysis.compute(icfg,
				new LinkedHashSet<>(threadIds), settings.joinPrecision());

		final GhostVariableManager ghostVars = createGhostVariablesIfEnabled(settings, script, symbolTable, threadIds,
				icfg, locationIds, activityPreanalysis.getMultiForkedThreads());
		concurrentTools.configureStaticAnalysis(ghostVars, activityPreanalysis);
		final AbstractLocationPartitionedDomain partitionedDomain =
				usesLocationPartitioning(settings) && ghostVars != null
				? AbstractLocationPartitionedDomain.create(baseDomain, tools,
						ghostVars.getLocationTermVariablesByThread())
				: null;
		if (partitionedDomain != null) {
			logger.info("Abstract-location partitioned domain enabled");
			concurrentTools.setLocationPartitionedDomain(partitionedDomain);
		}
		final IDomain domain = partitionedDomain != null ? partitionedDomain : baseDomain;
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable,
				ghostVars, locationIds, icfg.getProcedureEntryNodes());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services, script,
				factory, symbolTable, true);
		final InterferenceEdgeTraverser edgeTraverser = new InterferenceEdgeTraverser(icfg, translator);
		final IInterferenceFactory interferenceFactory = createInterferenceFactory(
				settings.interferenceApplicatorType(), icfg, edgeTraverser, translator, postcondition, domain, factory,
				script);
		logger.info("Interference method: %s (%s)", settings.interferenceApplicatorType(),
				interferenceFactory == null ? "None" : interferenceFactory.getClass().getSimpleName());
		logger.info("Interference grouping: abstract-location pairs via %s", settings.locationAbstractionType());

		final ThreadModularProofChecker proofChecker = settings.proofCheck()
				? new ThreadModularProofChecker(icfg, postcondition, translator, domain, ghostVars,
						activityPreanalysis, activityPreanalysis.getMultiForkedThreads(), true)
				: null;

		return new SetupResult(threadIds, domain, defaultLoopSumFactory, interferenceFactory, postcondition,
				proofChecker, joinedThreads, locationIds);
	}

	private static boolean usesLocationPartitioning(final ThreadModularSifaSettings settings) {
		if (!settings.useBuckets()) {
			return false;
		}
		final InterferenceApplicatorType type = settings.interferenceApplicatorType();
		return type == InterferenceApplicatorType.STRONGEST_POSTCONDITION;
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
		final var concurrency = icfg.getCfgSmtToolkit().getConcurrencyInformation();
		final Map<List<Term>, String> threadByForkId = concurrency.getThreadInstanceMap().keySet().stream()
				.collect(Collectors.toMap(fork -> List.of(fork.getForkSmtArguments().getThreadIdArguments().terms()),
						fork -> fork.getNameOfForkedProcedure(), (left, right) -> left, LinkedHashMap::new));
		return concurrency.getJoinTransitions().stream()
				.map(join -> threadByForkId.get(List.of(join.getJoinSmtArguments().getThreadIdArguments().terms())))
				.filter(Objects::nonNull).collect(Collectors.toSet());
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg, final Set<String> joinedThreads) {
		final var locationAbstraction = new LocationAbstraction<>();
		return new HashMap<>(locationAbstraction
				.computeLocationAbstraction(settings.locationAbstractionType(), services, icfg).toMap());
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
			final IIcfg<IcfgLocation> icfg, final InterferenceEdgeTraverser edgeTraverser,
			final TransFormulaToInterferencePredicate translator, final RelationalPredicatePostcondition postcondition,
			final IDomain domain, final BasicPredicateFactory factory, final ManagedScript script) {
		return switch (applicatorType) {
		case STRONGEST_POSTCONDITION ->
			new StrongestPostconditionInterferenceFactory(edgeTraverser, translator, postcondition, factory, script);
		case PREPOST ->
			new PrePostInterferenceFactory(edgeTraverser, translator, postcondition, script, factory);
		case GUARDED_EXACT_UPDATE ->
			new GuardedUpdateInterferenceFactory(icfg, translator, postcondition, script, factory);
		case POST_STATE ->
			new PostStateInterferenceFactory(edgeTraverser, translator, postcondition, domain, factory, script);
		case UNARY_GLOBALS ->
			new UnaryGlobalInterferenceFactory(edgeTraverser, translator.getServices(), translator, postcondition,
					domain, factory, script);
		case NONE -> null;
		};
	}

	public static record SetupResult(List<String> threadIds, IDomain domain,
			Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			IInterferenceFactory interferenceFactory, RelationalPredicatePostcondition postcondition,
			ThreadModularProofChecker proofChecker, Set<String> joinedThreads,
			Map<IcfgLocation, Integer> abstractLocationIds) {
	}
}
