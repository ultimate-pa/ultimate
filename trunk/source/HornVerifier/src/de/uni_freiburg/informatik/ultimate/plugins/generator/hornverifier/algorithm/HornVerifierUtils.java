package de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.algorithm;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.IPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornverifier.HornVerifierPreferenceInitializer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HornVerifierUtils {
	private static final String SCRIPT_BASENAME = "dumped";

	private HornVerifierUtils() {
	}

	public static ManagedScript createSolver(final IUltimateServiceProvider services) {
		final IPreferenceProvider prefs = services.getPreferenceProvider(Activator.PLUGIN_ID);
		final String dumpDir = prefs.getString(HornVerifierPreferenceInitializer.LABEL_DUMP_DIR);
		final boolean dumpToFile = prefs.getBoolean(HornVerifierPreferenceInitializer.LABEL_DUMP_TO_FILE);
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setUseExternalSolver(ExternalSolver.Z3, Logics.HORN)
						.setDumpSmtScriptToFile(dumpToFile, dumpDir, SCRIPT_BASENAME, false);
		return new ManagedScript(services,
				SolverBuilder.buildAndInitializeSolver(services, solverSettings, Activator.PLUGIN_NAME));
	}

	public static HornClauseSystem createHornClauses(final IIcfg<IcfgLocation> icfg, final ManagedScript managedScript,
			final int maximumNumberOfThreads) {
		final Pair<Map<String, Integer>, Set<String>> pair =
				getNumberOfThreadsAndExceedingBound(icfg, maximumNumberOfThreads);
		final Map<String, Integer> numberOfThreads = pair.getFirst();
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		final List<IcfgEdge> inductivityEdges = new ArrayList<>();
		final List<IcfgEdge> nonInterferenceEdges = new ArrayList<>();
		final Set<IProgramVar> readVariables = new HashSet<>();
		for (final String proc : numberOfThreads.keySet()) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			final boolean isUnboundedThread = pair.getSecond().contains(proc);
			while (edges.hasNext()) {
				final IcfgEdge edge = edges.next();
				inductivityEdges.add(edge);
				if (isUnboundedThread) {
					nonInterferenceEdges.add(edge);
				}
				readVariables.addAll(edge.getTransformula().getInVars().keySet());
			}
		}
		// TODO: This is only an approximation for now and should be improved
		final Predicate<IProgramVar> filter = x -> !x.getSort().isArraySort() && readVariables.contains(x);
		final HornClauseSystem result =
				new HornClauseSystem(numberOfThreads, managedScript, icfg.getCfgSmtToolkit(), filter);
		result.assertInitially(icfg.getInitialNodes());
		final Set<IcfgLocation> errorNodes =
				icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toSet());
		result.assertSafety(errorNodes);
		for (final IcfgEdge edge : inductivityEdges) {
			// TODO: Add the handling of joins (needs thread id?)
			if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
				final String forked = ((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure();
				result.assertInductivity(List.of(edge.getSource()), edge,
						List.of(edge.getTarget(), entryNodes.get(forked)));
			}
			result.assertInductivity(edge);
		}
		nonInterferenceEdges.forEach(result::assertNonInterference);
		return result;
	}

	// TODO: This is very inaccurate, we should consider the reachability of the forks instead!
	private static Pair<Map<String, Integer>, Set<String>> getNumberOfThreadsAndExceedingBound(final IIcfg<?> icfg,
			final int maximum) {
		final var instanceMap = icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap();
		final Map<String, Integer> countMap =
				icfg.getInitialNodes().stream().collect(Collectors.toMap(IcfgLocation::getProcedure, x -> 1));
		final Set<String> unboundedThreads = new HashSet<>();
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final var entry : instanceMap.entrySet()) {
				final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork = entry.getKey();
				if (!countMap.containsKey(fork.getPrecedingProcedure())) {
					continue;
				}
				final String proc = fork.getNameOfForkedProcedure();
				final int count = countMap.getOrDefault(proc, 0);
				if (count < maximum) {
					changed = true;
					countMap.put(proc, count + 1);
				} else {
					unboundedThreads.add(proc);
				}
			}
		}
		return new Pair<>(countMap, unboundedThreads);
	}
}
