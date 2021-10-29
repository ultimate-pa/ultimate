package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.horn;

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

public class Cfg2HornClauseUtils {
	private Cfg2HornClauseUtils() {
	}

	public static ManagedScript createSolver(final IUltimateServiceProvider services) {
		// TODO: Other solvers?
		final SolverSettings solverSettings = SolverBuilder.constructSolverSettings()
				.setSolverMode(SolverMode.External_DefaultMode).setUseExternalSolver(ExternalSolver.Z3, Logics.HORN);
		return new ManagedScript(services,
				SolverBuilder.buildAndInitializeSolver(services, solverSettings, "HornSolver"));
	}

	public static Cfg2HornClauses createHornClauses(final IIcfg<IcfgLocation> icfg, final ManagedScript managedScript,
			final int maximumNumberOfThreads) {
		final Map<String, Integer> numberOfThreads = getNumberOfThreads(icfg, maximumNumberOfThreads);
		final Cfg2HornClauses result = new Cfg2HornClauses(numberOfThreads, managedScript, icfg.getCfgSmtToolkit());
		result.assertInitially(icfg.getInitialNodes());
		final Set<IcfgLocation> errorNodes =
				icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toSet());
		result.assertSafety(errorNodes);
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		for (final String proc : numberOfThreads.keySet()) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			while (edges.hasNext()) {
				// TODO: Add the handling of joins (needs thread id?)
				final IcfgEdge edge = edges.next();
				if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
					final String forked = ((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure();
					result.assertInductivity(List.of(edge.getSource()), edge,
							List.of(edge.getTarget(), entryNodes.get(forked)));
				}
				result.assertInductivity(edge);
			}
		}
		// TODO: For unbounded threads we need non-interference!
		return result;
	}

	public static Map<String, Integer> getNumberOfThreads(final IIcfg<IcfgLocation> icfg, final int maximum) {
		final var instanceMap = icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap();
		final Map<String, Integer> result =
				icfg.getInitialNodes().stream().collect(Collectors.toMap(IcfgLocation::getProcedure, x -> 1));
		boolean changed = true;
		while (changed) {
			changed = false;
			for (final var entry : instanceMap.entrySet()) {
				final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork = entry.getKey();
				if (!result.containsKey(fork.getPrecedingProcedure())) {
					continue;
				}
				final String proc = fork.getNameOfForkedProcedure();
				final int count = result.getOrDefault(proc, 0);
				if (count < maximum) {
					changed = true;
					result.put(proc, count + 1);
				}
			}
		}
		return result;
	}
}
