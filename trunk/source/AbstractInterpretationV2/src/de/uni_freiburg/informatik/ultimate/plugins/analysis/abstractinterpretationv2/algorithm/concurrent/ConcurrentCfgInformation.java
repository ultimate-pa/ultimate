package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocationIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class ConcurrentCfgInformation<ACTION, LOC extends IcfgLocation> {
	private final IIcfg<? extends LOC> mIcfg;
	private final HashRelation<String, LOC> mProceduresToForkLocations;
	private final Set<String> mUnboundedThreads;
	private final List<String> mTopologicalOrder;
	// private final HashRelation<LOC, String> mActiveThreadPerLocation;

	public ConcurrentCfgInformation(final IIcfg<? extends LOC> icfg) {
		mIcfg = icfg;
		mUnboundedThreads = IcfgUtils.getForksInLoop(icfg).stream().map(x -> x.getNameOfForkedProcedure())
				.collect(Collectors.toSet());
		mProceduresToForkLocations = new HashRelation<>();
		mTopologicalOrder = computeTopologicalOrder();
		final HashRelation<String, String> forkRelation = new HashRelation<>();
		getForks().forEach(x -> forkRelation.addPair(x.getPrecedingProcedure(), x.getNameOfForkedProcedure()));
		final HashRelation<String, String> closureDepending = closure(forkRelation);
		final HashRelation<String, String> dependingOn = computeDependingProcedures(closureDepending, forkRelation);
		// mActiveThreadPerLocation = computeInterferingThreadsPerLocation(...);
		getForks().forEach(x -> mProceduresToForkLocations.addPair(x.getNameOfForkedProcedure(), (LOC) x.getSource()));
	}

	private Set<IIcfgForkTransitionThreadCurrent<IcfgLocation>> getForks() {
		return mIcfg.getCfgSmtToolkit().getConcurrencyInformation().getThreadInstanceMap().keySet();
	}

	public Set<LOC> getForkLocations(final String procedure) {
		return mProceduresToForkLocations.getImage(procedure);
	}

	public List<String> getTopologicalProcedureOrder() {
		return mTopologicalOrder;
	}

	private List<String> computeTopologicalOrder() {
		final Map<String, Set<String>> forkRelation = getForkRelation();
		final List<String> result = new ArrayList<>();
		final Map<String, Integer> forkCounter = new HashMap<>();
		forkRelation.forEach((k, v) -> forkCounter.put(k, 0));
		getForks().forEach(
				x -> forkCounter.put(x.getNameOfForkedProcedure(), forkCounter.get(x.getNameOfForkedProcedure()) + 1));
		final HashRelation<Integer, String> numberOfIncomingForks = new HashRelation<>();
		forkRelation.forEach((k, v) -> numberOfIncomingForks.addPair(forkCounter.get(k), k));
		Set<String> noIncoming = numberOfIncomingForks.removeDomainElement(0);
		final Set<String> remaining = new HashSet<>(forkRelation.keySet());
		while (!noIncoming.isEmpty()) {
			result.addAll(noIncoming);
			remaining.removeAll(noIncoming);
			final Set<String> newNoIncoming = new HashSet<>();
			for (final String thread : noIncoming) {
				for (final String forked : forkRelation.get(thread)) {
					final Integer oldValue = forkCounter.get(forked);
					numberOfIncomingForks.removePair(oldValue, forked);
					if (oldValue == 1) {
						newNoIncoming.add(forked);
					} else {
						final Integer newValue = oldValue - 1;
						forkCounter.put(forked, newValue);
						numberOfIncomingForks.addPair(newValue, forked);
					}
				}
			}
			noIncoming = newNoIncoming;
		}
		// Add all remaining procedures (in the case that a loop was found)
		result.addAll(remaining);
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

	public Set<String> getInterferingThreads(final LOC location) {
		// TODO: Do something more precise based on the flow of the forks
		// (e.g. there should be no interference before a fork)
		// return mActiveThreadPerLocation.getImage(location);
		final Set<String> result = new HashSet<>(mIcfg.getProcedureEntryNodes().keySet());
		final String ownProcedure = location.getProcedure();
		if (getForkLocations(ownProcedure).size() <= 1 && !mUnboundedThreads.contains(ownProcedure)) {
			result.remove(ownProcedure);
		}
		return result;
	}

	private List<String> getTopologicalOrderReverse() {
		final Map<String, Set<String>> forkRelation = getForkRelation();
		final HashRelation<Integer, String> numberOfForks = new HashRelation<>();
		forkRelation.forEach((t, dep) -> numberOfForks.addPair(dep.size(), t));
		final List<String> result = new ArrayList<>();
		while (!numberOfForks.isEmpty()) {
			final Set<String> candidates = numberOfForks.removeDomainElement(0);
			if (candidates == null || candidates.isEmpty()) {
				// TODO: What should we do in that case?
				throw new UnsupportedOperationException("Cycle found");
			}
			result.addAll(candidates);
			for (final String t : candidates) {
				// TODO: For one usecase we actually need the fork locations (and know if there are multiple)
				for (final LOC loc : getForkLocations(t)) {
					final String forking = loc.getProcedure();
					final Set<String> forked = forkRelation.get(forking);
					numberOfForks.removePair(forked.size(), forking);
					numberOfForks.addPair(forked.size() - 1, forking);
					forked.remove(t);
				}
			}
		}
		return result;
	}

	private Map<String, Set<String>> getForkRelation() {
		final Map<String, Set<String>> result = new HashMap<>();
		final ArrayDeque<String> worklist = new ArrayDeque<>();
		mIcfg.getInitialNodes().stream().map(IcfgLocation::getProcedure).forEach(x -> result.put(x, new HashSet<>()));
		worklist.addAll(result.keySet());
		while (!worklist.isEmpty()) {
			final String currentThread = worklist.pop();
			for (final IIcfgForkTransitionThreadCurrent<IcfgLocation> fork : getForks()) {
				if (!currentThread.equals(fork.getPrecedingProcedure())) {
					continue;
				}
				final String newThread = fork.getNameOfForkedProcedure();
				result.get(currentThread).add(newThread);
				result.computeIfAbsent(newThread, x -> {
					worklist.add(x);
					return new HashSet<>();
				});
			}
		}
		return result;
	}

	private HashRelation<LOC, String> computeInterferingThreadsPerLocation(
			final HashRelation<String, String> initialActiveThreads,
			final HashRelation<IIcfgForkTransitionThreadCurrent<IcfgLocation>, String> activeThreadsAfterFork) {
		final HashRelation<LOC, String> result = new HashRelation<>();
		for (final Entry<String, ? extends LOC> entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			final String thread = entry.getKey();
			final Set<String> activeThreads = initialActiveThreads.getImage(thread);
			if (!activeThreads.isEmpty()) {
				new IcfgLocationIterator<>(entry.getValue())
						.forEachRemaining(x -> result.addAllPairs(x, activeThreads));
			}
			for (final var fork : getForks()) {
				if (!fork.getPrecedingProcedure().equals(thread)) {
					continue;
				}
				new IcfgLocationIterator<>(fork.getTarget())
						.forEachRemaining(x -> result.addAllPairs((LOC) x, activeThreadsAfterFork.getImage(fork)));
			}
		}
		return result;
	}

	private static HashRelation<String, String> closure(final HashRelation<String, String> map) {
		final HashRelation<String, String> result = new HashRelation<>(map);
		boolean changes = true;
		while (changes) {
			changes = false;
			for (final Entry<String, HashSet<String>> entry : result.entrySet()) {
				// TODO: We need to create a copy to avoid ConcurrentModificationException, is there a better way?
				for (final String forked : new HashSet<>(entry.getValue())) {
					final String current = entry.getKey();
					if (result.getImage(forked).stream().anyMatch(x -> !entry.getValue().contains(x))) {
						result.addAllPairs(current, result.getImage(forked));
						changes = true;
					}
				}
			}
		}
		return result;
	}

	private HashRelation<String, String> computeDependingProcedures(final HashRelation<String, String> closureForks,
			final HashRelation<String, String> forkRelation) {
		final HashRelation<String, String> result = new HashRelation<>();
		final ArrayDeque<String> worklist = new ArrayDeque<>();
		final Set<String> added = new HashSet<>();
		final String startitem = mTopologicalOrder.get(0);
		worklist.add(startitem);
		added.add(startitem);
		while (!worklist.isEmpty()) {
			final String currentItem = worklist.poll();
			final Set<String> forkedThreads = forkRelation.getImage(currentItem);
			for (final String forked : forkedThreads) {
				// copy all entries von item into child
				result.addAllPairs(forked, result.getImage(currentItem));
				// add parent
				result.addPair(forked, currentItem);
				// add closure over all other children
				for (final String child : forkedThreads) {
					if (child.equals(forked)) {
						continue;
					}
					result.addPair(forked, child);
					result.addAllPairs(forked, closureForks.getImage(child));
				}

				if (!added.contains(forked)) {
					worklist.add(forked);
					added.add(forked);
				}
			}
		}
		return result;
	}
}
