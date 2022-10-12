package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm.concurrent;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

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

public class ConcurrentIcfgAnalyzer<ACTION, LOC extends IcfgLocation> {
	private final IIcfg<? extends LOC> mIcfg;
	private final HashRelation<String, LOC> mProceduresToForkLocations;
	private final List<String> mTopologicalOrder;
	private final HashRelation<String, ACTION> mThreadsToWrites;
	private final HashRelation<ACTION, IProgramVarOrConst> mSharedWrites;
	private final HashRelation<LOC, ACTION> mInterferingWrites;
	private final HashRelation<String, IIcfgForkTransitionThreadCurrent<IcfgLocation>> mThreadsToForks;
	private final Set<String> mUnboundedThreads;

	public ConcurrentIcfgAnalyzer(final IIcfg<? extends LOC> icfg) {
		mIcfg = icfg;
		mUnboundedThreads = IcfgUtils.getForksInLoop(icfg).stream().map(x -> x.getNameOfForkedProcedure())
				.collect(Collectors.toSet());
		mTopologicalOrder = computeTopologicalOrder();
		mThreadsToWrites = new HashRelation<>();
		mSharedWrites = new HashRelation<>();
		mInterferingWrites = new HashRelation<>();
		mThreadsToForks = new HashRelation<>();
		mProceduresToForkLocations = new HashRelation<>();
		computeSharedWrites();
		final HashRelation<String, String> forkRelation = new HashRelation<>();
		for (final var fork : getForks()) {
			final String forking = fork.getPrecedingProcedure();
			final String forked = fork.getNameOfForkedProcedure();
			mThreadsToForks.addPair(forking, fork);
			mProceduresToForkLocations.addPair(forked, (LOC) fork.getSource());
			forkRelation.addPair(forking, forked);
		}
		final HashRelation<String, String> closureForks = DataStructureUtils.transitiveClosure(forkRelation);
		mTopologicalOrder.forEach(x -> addInterferences(x, closureForks));
	}

	private void addInterferences(final String thread, final HashRelation<String, String> closureForks) {
		final Set<ACTION> initialInterferences = new HashSet<>();
		// Add all interferences from each fork location
		// TODO: Does this work correctly, if the fork relation has a cycle?
		for (final LOC forkedBy : mProceduresToForkLocations.getImage(thread)) {
			initialInterferences.addAll(mInterferingWrites.getImage(forkedBy));
		}
		for (final LOC loc : mIcfg.getProgramPoints().get(thread).values()) {
			mInterferingWrites.addAllPairs(loc, initialInterferences);
		}
		for (final var fork : mThreadsToForks.getImage(thread)) {
			final Set<ACTION> interferingWrites =
					getTransitivelyForkedWrites(fork.getNameOfForkedProcedure(), closureForks);
			final Collection<? extends LOC> locsOfForkedThread =
					mIcfg.getProgramPoints().get(fork.getNameOfForkedProcedure()).values();
			new IcfgLocationIterator<>((LOC) fork.getTarget()).forEachRemaining(loc -> {
				// Add all transitively forked writes to every location after the fork
				mInterferingWrites.addAllPairs(loc, interferingWrites);
				// Add all writes that occur after the fork to every location of the forked thread
				locsOfForkedThread
						.forEach(x -> mInterferingWrites.addAllPairs(x, getSharedWritesAtLocation(loc, closureForks)));
			});
		}
	}

	private Set<ACTION> getSharedWritesAtLocation(final LOC loc, final HashRelation<String, String> closureForks) {
		final Set<ACTION> result = new HashSet<>();
		for (final IcfgEdge edge : loc.getOutgoingEdges()) {
			if (!mSharedWrites.hasEmptyImage((ACTION) edge)) {
				result.add((ACTION) edge);
			} else if (edge instanceof IIcfgForkTransitionThreadCurrent) {
				final Set<ACTION> transitiveWrites = getTransitivelyForkedWrites(
						((IIcfgForkTransitionThreadCurrent<?>) edge).getNameOfForkedProcedure(), closureForks);
				result.addAll(transitiveWrites);
			}
		}
		return result;
	}

	private Set<ACTION> getTransitivelyForkedWrites(final String thread,
			final HashRelation<String, String> closureForks) {
		return Stream.concat(Stream.of(thread), closureForks.getImage(thread).stream())
				.flatMap(x -> mThreadsToWrites.getImage(x).stream()).collect(Collectors.toSet());
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

	public Set<ACTION> getInterferingWrites(final LOC location) {
		return mInterferingWrites.getImage(location);
	}

	public HashRelation<ACTION, IProgramVarOrConst> getSharedWrites() {
		return mSharedWrites;
	}

	private void computeSharedWrites() {
		final HashRelation<ACTION, IProgramVarOrConst> writesToVariables = new HashRelation<>();
		final HashRelation<IProgramVar, String> writesToProcedures = new HashRelation<>();
		final HashRelation<IProgramVar, String> readsToProcedures = new HashRelation<>();
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
				final ACTION write = entry.getKey();
				mSharedWrites.addAllPairs(write, writtenSharedVars);
				mThreadsToWrites.addPair(((IcfgEdge) write).getPrecedingProcedure(), write);
			}
		}
	}

	private boolean isSharedVariable(final IProgramVar var, final HashRelation<IProgramVar, String> writesToProcedures,
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
		// readingProcedures and writingProcedures are both singletons, return true iff they are different
		if (!readingProcedures.equals(writingProcedures)) {
			return true;
		}
		// ... or iff it's the same thread, but can interfere with itself (unbounded or forked multiple times)
		final String thread = readingProcedures.iterator().next();
		return mUnboundedThreads.contains(thread) || mProceduresToForkLocations.getImage(thread).size() > 1;
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
}
