package de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.setup;

import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.sifa.DagInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.IcfgInterpreter;
import de.uni_freiburg.informatik.ultimate.lib.sifa.SymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ConcurrentSymbolicTools;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.cfg.LocationAbstraction;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.ghostvariables.GhostVariableManager;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.IInterference;
import de.uni_freiburg.informatik.ultimate.lib.sifa.concurrent.interference.InterferenceFactory;
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
		final Set<String> threadIds = discoverThreadIds(icfg);
		final Map<IcfgLocation, Integer> locationIds = computeLocationIds(settings, services, icfg);

		final GhostVariableManager ghostVars = createGhostVariablesIfEnabled(settings, script, symbolTable, threadIds,
				icfg, locationIds);
		final ThreadActivityPreanalysis activityPreanalysis = ThreadActivityPreanalysis.compute(icfg, threadIds);
		concurrentTools.configureStaticAnalysis(ghostVars, activityPreanalysis);
		final IDomain analysisDomain = baseDomain;
		final var translator = new TransFormulaToInterferencePredicate(services, script, factory, symbolTable,
				ghostVars, locationIds, icfg.getProcedureEntryNodes(), settings.quantifierEliminationMode());
		final RelationalPredicatePostcondition postcondition = new RelationalPredicatePostcondition(services, script,
				factory, symbolTable, true, settings.quantifierEliminationMode());
		final InterferenceFactory interferenceFactory = new InterferenceFactory(translator, analysisDomain, script,
				factory, settings.interferenceMergeMode(), settings.interferenceType());
		final IInterference interferenceBuilder = interferenceFactory.createBuilder();

		final boolean ghostInstrumentationEnabled = ghostVars != null;
		final boolean includeInterferencePreState = true;
		final ThreadModularProofChecker proofChecker = new ThreadModularProofChecker(icfg.getCfgSmtToolkit(),
				postcondition, translator, analysisDomain, ghostInstrumentationEnabled, includeInterferencePreState);

		return new SetupResult(threadIds, analysisDomain, defaultLoopSumFactory, interferenceFactory,
				interferenceBuilder, postcondition, proofChecker);
	}

	private static Set<String> discoverThreadIds(final IIcfg<IcfgLocation> icfg) {
		final Set<String> ids = new LinkedHashSet<>();
		ids.add(MAIN_THREAD);
		for (final var fork : icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet()) {
			ids.add(fork.getNameOfForkedProcedure());
		}
		return ids;
	}

	private static Map<IcfgLocation, Integer> computeLocationIds(final ThreadModularSifaSettings settings,
			final IUltimateServiceProvider services, final IIcfg<IcfgLocation> icfg) {
		if (settings.locationTrackingMode() == LocationTrackingMode.NONE) {
			return Map.of();
		}
		final var locationAbstraction = new LocationAbstraction<>();
		return locationAbstraction.computeLocationAbstraction(settings.locationAbstractionType(), services, icfg)
				.toMap();
	}

	private static GhostVariableManager createGhostVariablesIfEnabled(final ThreadModularSifaSettings settings,
			final ManagedScript script, final PrimedDefaultIcfgSymbolTable symbolTable, final Set<String> threadIds,
			final IIcfg<IcfgLocation> icfg, final Map<IcfgLocation, Integer> locationIds) {
		if (!settings.useGhostLocations()) {
			return null;
		}
		return GhostVariableManager.create(script, locationIds, threadIds, icfg.getProcedureEntryNodes(), symbolTable,
				true);
	}

	public static record SetupResult(Set<String> threadIds, IDomain analysisDomain,
			Function<IcfgInterpreter, Function<DagInterpreter, ILoopSummarizer>> loopSumFactory,
			InterferenceFactory interferenceFactory, IInterference interferenceBuilder,
			RelationalPredicatePostcondition postcondition, ThreadModularProofChecker proofChecker) {
	}
}
