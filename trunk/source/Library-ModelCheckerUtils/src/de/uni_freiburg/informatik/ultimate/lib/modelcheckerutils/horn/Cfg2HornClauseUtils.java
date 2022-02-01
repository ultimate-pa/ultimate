package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.horn;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.ExternalSolver;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverMode;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.solverbuilder.SolverBuilder.SolverSettings;
import de.uni_freiburg.informatik.ultimate.logic.Logics;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class Cfg2HornClauseUtils {
	private Cfg2HornClauseUtils() {
	}

	public static ManagedScript createSolver(final IUltimateServiceProvider services) {
		// TODO: Other solvers?
		final SolverSettings solverSettings =
				SolverBuilder.constructSolverSettings().setSolverMode(SolverMode.External_ModelsAndUnsatCoreMode)
						.setUseExternalSolver(ExternalSolver.Z3, Logics.HORN);
		return new ManagedScript(services,
				SolverBuilder.buildAndInitializeSolver(services, solverSettings, "HornSolver"));
	}

	public static Cfg2HornClauses createHornClauses(final IIcfg<IcfgLocation> icfg, final ManagedScript managedScript,
			final int maximumNumberOfThreads) {
		final Pair<Map<String, Integer>, Set<String>> pair =
				getNumberOfThreadsAndExceedingBound(icfg, maximumNumberOfThreads);
		final Map<String, Integer> numberOfThreads = pair.getFirst();
		final Cfg2HornClauses result = new Cfg2HornClauses(numberOfThreads, managedScript, icfg.getCfgSmtToolkit());
		result.assertInitially(icfg.getInitialNodes());
		final Set<IcfgLocation> errorNodes =
				icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toSet());
		result.assertSafety(errorNodes);
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		for (final String proc : numberOfThreads.keySet()) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			final boolean isUnbounded = pair.getSecond().contains(proc);
			while (edges.hasNext()) {
				// TODO: Add the handling of joins (needs thread id?)
				final IcfgEdge edge = edges.next();
				if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
					final String forked = ((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure();
					result.assertInductivity(List.of(edge.getSource()), edge,
							List.of(edge.getTarget(), entryNodes.get(forked)));
				}
				result.assertInductivity(edge);
				if (isUnbounded) {
					result.assertNonInterference(edge);
				}
			}
		}
		return result;
	}

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

	public static Map<String, Integer> getNumberOfThreads(final IIcfg<?> icfg, final int maximum) {
		return getNumberOfThreadsAndExceedingBound(icfg, maximum).getFirst();
	}
}
