package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.IcfgToChcObserver.IChcProvider;

/**
 * ChcProvider for concurrent programs based on the icfg.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ChcProviderConcurrent implements IChcProvider {
	private final ManagedScript mMgdScript;
	private final HcSymbolTable mHcSymbolTable;

	private static final int MAXIMUM_NUMBER_OF_THREADS = 2;

	public ChcProviderConcurrent(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable) {
		mMgdScript = mgdScript;
		mHcSymbolTable = hcSymbolTable;
	}

	@Override
	public Collection<HornClause> getHornClauses(final IIcfg<IcfgLocation> icfg) {
		final var forksInLoops = IcfgUtils.getForksInLoop(icfg);
		final var instanceMap = icfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap();
		final Map<String, Integer> numberOfThreads = new HashMap<>();
		icfg.getInitialNodes().forEach(x -> numberOfThreads.put(x.getProcedure(), 1));
		final List<String> unboundedThreads = new ArrayList<>();
		// TODO: This needs to be more accurate in general
		for (final var fork : instanceMap.keySet()) {
			final String procedure = fork.getNameOfForkedProcedure();
			// TODO: Only add if fork is reachable
			if (forksInLoops.contains(fork)) {
				numberOfThreads.put(procedure, MAXIMUM_NUMBER_OF_THREADS);
				unboundedThreads.add(procedure);
			} else {
				final Integer oldCount = numberOfThreads.getOrDefault(procedure, 0);
				if (oldCount == MAXIMUM_NUMBER_OF_THREADS) {
					unboundedThreads.add(procedure);
				} else {
					numberOfThreads.put(procedure, oldCount + 1);
				}
			}
		}
		final IcfgToChcConcurrent factory = new IcfgToChcConcurrent(numberOfThreads, mMgdScript,
				icfg.getCfgSmtToolkit(), mHcSymbolTable, x -> true);
		final List<HornClause> result = new ArrayList<>();
		result.add(factory.getInitialClause(icfg.getInitialNodes()));
		final Set<IcfgLocation> errorNodes =
				icfg.getProcedureErrorNodes().values().stream().flatMap(Set::stream).collect(Collectors.toSet());
		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		result.addAll(factory.getSafetyClauses(errorNodes));
		for (final String proc : numberOfThreads.keySet()) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			while (edges.hasNext()) {
				// TODO: Add the handling of joins (needs thread id?)
				final IcfgEdge edge = edges.next();
				if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
					final String forked = ((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure();
					result.addAll(factory.getInductivityClauses(List.of(edge.getSource()), edge,
							List.of(edge.getTarget(), entryNodes.get(forked))));
				}
				result.addAll(factory.getInductivityClauses(edge));
				if (unboundedThreads.contains(proc)) {
					result.add(factory.getNonInterferenceClause(edge));
				}
			}
		}
		return result;
	}
}
