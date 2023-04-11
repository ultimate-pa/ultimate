package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.chc.HcSymbolTable;
import de.uni_freiburg.informatik.ultimate.lib.chc.HornClause;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.ManagedScript;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.IcfgToChcObserver.IChcProvider;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Triple;

/**
 * ChcProvider for concurrent programs based on the icfg.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ChcProviderConcurrent implements IChcProvider {
	public enum Mode {
		SINGLE_MAIN_THREAD, PARAMETRIC
	}

	protected final ManagedScript mMgdScript;
	protected final HcSymbolTable mHcSymbolTable;
	protected final Mode mMode;
	protected final int mLevel;

	public ChcProviderConcurrent(final ManagedScript mgdScript, final HcSymbolTable hcSymbolTable, final Mode mode,
			final int level) {
		mMgdScript = mgdScript;
		mHcSymbolTable = hcSymbolTable;
		mMode = mode;
		mLevel = level;

		assert level >= 1;
	}

	@Override
	public Collection<HornClause> getHornClauses(final IIcfg<IcfgLocation> icfg) {
		final var threadBounds = getThreadNumbersAndUnboundedThreads(icfg);
		final var numberOfThreads = threadBounds.getFirst();
		final var unboundedThreads = threadBounds.getSecond();

		final var factory = createFactory(numberOfThreads, icfg);
		final List<HornClause> result = new ArrayList<>();

		final var initialClause = factory.buildInitialClause(getInitialLocations(icfg, factory.getInstances())).build();
		result.add(initialClause);

		final Map<String, IcfgLocation> entryNodes = icfg.getProcedureEntryNodes();
		for (final String proc : numberOfThreads.keySet()) {
			final IcfgEdgeIterator edges = new IcfgEdgeIterator(entryNodes.get(proc).getOutgoingEdges());
			while (edges.hasNext()) {
				final IcfgEdge edge = edges.next();
				for (final var prePost : getCartesianPrePostProduct(factory, icfg, edge)) {
					final var clause = factory
							.buildInductivityClause(edge, prePost.getFirst(), prePost.getSecond(), prePost.getThird())
							.build();
					result.add(clause);
				}

				if (unboundedThreads.contains(proc)) {
					result.add(factory.buildNonInterferenceClause(edge).build());
				}
			}
		}

		final var errorLocs = getErrorLocations(icfg, factory.getInstances());
		for (final var pair : errorLocs) {
			final var safetyClause = factory.buildSafetyClause(pair.getFirst(), pair.getSecond()).build();
			result.add(safetyClause);
		}

		return result;
	}

	private static List<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>
			getCartesianPrePostProduct(final ThreadModularHornClauseProvider factory, final IIcfg<?> icfg,
					final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>) {
			final var forkCurrent = (IIcfgForkTransitionThreadCurrent<?>) edge;
			final var forkEntry = icfg.getProcedureEntryNodes().get(forkCurrent.getNameOfForkedProcedure());
			final var result =
					new ArrayList<Triple<Map<ThreadInstance, IcfgLocation>, Map<ThreadInstance, IcfgLocation>, ThreadInstance>>();
			for (final var instance : factory.getInstances(edge.getPrecedingProcedure())) {
				final var preds = Map.of(instance, edge.getSource());
				for (final var forked : factory.getInstances(forkCurrent.getNameOfForkedProcedure())) {
					if (Objects.equals(instance, forked)) {
						continue;
					}
					final var succs = Map.of(instance, edge.getTarget(), forked, forkEntry);
					result.add(new Triple<>(preds, succs, instance));
				}
			}
			return result;
		}
		if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			assert false : "Joins not supported";
		}

		return factory.getInstances(edge.getPrecedingProcedure()).stream()
				.map(t -> new Triple<>(Map.of(t, edge.getSource()), Map.of(t, edge.getTarget()), t))
				.collect(Collectors.toList());
	}

	protected Pair<Map<String, Integer>, List<String>>
			getThreadNumbersAndUnboundedThreads(final IIcfg<IcfgLocation> icfg) {
		if (mMode == Mode.PARAMETRIC) {
			final var numberOfThreads =
					icfg.getInitialNodes().stream().collect(Collectors.toMap(loc -> loc.getProcedure(), loc -> mLevel));
			final var unbounded = List.copyOf(numberOfThreads.keySet());
			return new Pair<>(numberOfThreads, unbounded);
		}

		assert mMode == Mode.SINGLE_MAIN_THREAD : "Unknown mode: " + mMode;

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
				numberOfThreads.put(procedure, mLevel);
				unboundedThreads.add(procedure);
			} else {
				final Integer oldCount = numberOfThreads.getOrDefault(procedure, 0);
				if (oldCount == mLevel) {
					unboundedThreads.add(procedure);
				} else {
					numberOfThreads.put(procedure, oldCount + 1);
				}
			}
		}

		return new Pair<>(numberOfThreads, unboundedThreads);
	}

	protected Map<ThreadInstance, IcfgLocation> getInitialLocations(final IIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances) {
		switch (mMode) {
		case PARAMETRIC:
			// combine each initial location (usually there is only one) with ALL instances of its template
			return icfg
					.getInitialNodes().stream().flatMap(l -> instances.stream()
							.filter(i -> i.getTemplateName().equals(l.getProcedure())).map(i -> new Pair<>(i, l)))
					.collect(Collectors.toMap(Pair::getKey, Pair::getValue));
		case SINGLE_MAIN_THREAD:
			// combine each initial location (usually there is only one) with instance 0 of its template
			return icfg.getInitialNodes().stream()
					.collect(Collectors.toMap(l -> new ThreadInstance(l.getProcedure(), 0), l -> l));
		}
		throw new UnsupportedOperationException("Unknown mode: " + mMode);
	}

	protected List<Pair<ThreadInstance, IcfgLocation>> getErrorLocations(final IIcfg<IcfgLocation> icfg,
			final List<ThreadInstance> instances) {
		return icfg.getProcedureErrorNodes().entrySet().stream()
				.flatMap(e -> e.getValue().stream().map(l -> new Pair<>(e.getKey(), l))).flatMap(e -> instances.stream()
						.filter(i -> i.getTemplateName().equals(e.getKey())).map(i -> new Pair<>(i, e.getValue())))
				.collect(Collectors.toList());
	}

	protected ThreadModularHornClauseProvider createFactory(final Map<String, Integer> numberOfThreads,
			final IIcfg<IcfgLocation> icfg) {
		return new ThreadModularHornClauseProvider(numberOfThreads, mMgdScript, icfg.getCfgSmtToolkit(), mHcSymbolTable,
				x -> true);
	}
}
