package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class ConcurrentCfgInformation<ACTION, LOC extends IcfgLocation> {
	private final IIcfg<? extends LOC> mIcfg;
	private HashRelation<String, LOC> mProceduresToForkLocations;

	public ConcurrentCfgInformation(final IIcfg<? extends LOC> icfg) {
		mIcfg = icfg;
		getForks().forEach(x -> mProceduresToForkLocations.addPair(x.getNameOfForkedProcedure(), (LOC) x.getSource()));
	}

	private Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> getForks() {
		return mIcfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet();
	}

	public Set<LOC> getForkLocations(final String procedure) {
		return mProceduresToForkLocations.getImage(procedure);
	}

	// TODO: This seems rather inefficient and complicated. Can we do better?
	public List<String> getTopologicalProcedureOrder() {
		final Set<String> procedures = mIcfg.getProcedureEntryNodes().keySet();
		final Map<String, Integer> inGrad = new HashMap<>();
		for (final String procedure : procedures) {
			inGrad.put(procedure, 0);
		}

		final HashRelation<String, String> forks = new HashRelation<>();
		getForks().forEach(x -> forks.addPair(x.getPrecedingProcedure(), x.getNameOfForkedProcedure()));

		for (final var entry : forks.entrySet()) {
			for (final String forked : entry.getValue()) {
				inGrad.put(forked, inGrad.get(forked) + 1);
			}
		}

		final PriorityQueue<Pair<String, Integer>> pQueue =
				new PriorityQueue<>((x, y) -> x.getSecond() - y.getSecond());
		inGrad.forEach((k, v) -> pQueue.add(new Pair<>(k, v)));

		final Set<String> visited = new HashSet<>();
		final List<String> result = new ArrayList<>();
		while (!DataStructureUtils.difference(procedures, visited).isEmpty()) {
			final Pair<String, Integer> currentItem = pQueue.poll();
			if (currentItem.getSecond() == 0) {
				final String key = currentItem.getFirst();
				if (!visited.contains(key)) {
					result.add(key);
					visited.add(key);

					for (final String forked : forks.getImage(key)) {
						if (inGrad.get(forked) > 0) {
							inGrad.put(forked, inGrad.get(forked) - 1);
							pQueue.add(new Pair<>(forked, inGrad.get(forked)));
						}
					}
				}
				continue;
			}

			// cycle -> add others in arbitrary order
			for (final String procedure : DataStructureUtils.difference(procedures, visited)) {
				result.add(procedure);
			}
			break;
		}
		return result;
	}

	public HashRelation<ACTION, IProgramVarOrConst> getSharedWrites() {
		final HashRelation<ACTION, IProgramVarOrConst> writesToVariables = new HashRelation<>();
		final HashRelation<IProgramVar, String> writesToProcedures = new HashRelation<>();
		final HashRelation<IProgramVar, String> readsToProcedures = new HashRelation<>();
		final HashRelation<ACTION, IProgramVarOrConst> result = new HashRelation<>();
		for (final Entry<String, ?> entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			final String procedure = entry.getKey();
			final List<IcfgEdge> initalEdges = ((IcfgLocation) entry.getValue()).getOutgoingEdges();
			new IcfgEdgeIterator(initalEdges).forEachRemaining(edge -> {
				final TransFormula transformula = edge.getTransformula();
				for (final IProgramVar written : transformula.getAssignedVars()) {
					writesToVariables.addPair((ACTION) edge, written);
					writesToProcedures.addPair(written, procedure);
				}
				// TODO: Is this the best way to find reads?
				transformula.getInVars().forEach((k, v) -> readsToProcedures.addPair(k, procedure));
			});
		}
		final Set<IProgramVarOrConst> sharedVars = readsToProcedures.getDomain().stream()
				.filter(x -> isSharedVariable(x, writesToProcedures, readsToProcedures)).collect(Collectors.toSet());
		for (final Entry<ACTION, HashSet<IProgramVarOrConst>> entry : writesToVariables.entrySet()) {
			final Set<IProgramVarOrConst> writtenSharedVars =
					DataStructureUtils.intersection(entry.getValue(), sharedVars);
			if (!writtenSharedVars.isEmpty()) {
				result.addAllPairs(entry.getKey(), writtenSharedVars);
			}
		}
		return result;
	}

	private static boolean isSharedVariable(final IProgramVar var,
			final HashRelation<IProgramVar, String> writesToProcedures,
			final HashRelation<IProgramVar, String> readsToProcedures) {
		final Set<String> writingProcedures = writesToProcedures.getImage(var);
		if (writingProcedures.isEmpty()) {
			return false;
		}
		final Set<String> readingProcedures = readsToProcedures.getImage(var);
		if (readingProcedures.isEmpty()) {
			return false;
		}
		if (writingProcedures.size() > 1 || readingProcedures.size() > 1) {
			return true;
		}
		// readingProcedures and writingProcedures are both singleton, return true iff they are different
		return !readingProcedures.equals(writingProcedures);
	}
}
