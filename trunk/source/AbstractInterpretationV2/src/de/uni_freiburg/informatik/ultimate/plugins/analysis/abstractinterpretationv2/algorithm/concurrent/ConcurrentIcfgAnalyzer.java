/*
 * Copyright (C) 2022 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */
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
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Class to retrieve information of a concurrent ICFG (e.g. shared writes, information of concurrent control flow,...)
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class ConcurrentIcfgAnalyzer<ACTION, LOC extends IcfgLocation> {
	private final IIcfg<? extends LOC> mIcfg;
	private final HashRelation<String, LOC> mProceduresToForkLocations;
	private Pair<List<String>, Set<String>> mTopologicalOrderPair;
	private List<String> mTopologicalOrder;
	private final HashRelation<String, ACTION> mThreadsToWrites;
	private final HashRelation<ACTION, IProgramVarOrConst> mSharedWrites;
	private final HashRelation<LOC, ACTION> mInterferingWrites;
	private final HashRelation<String, IIcfgForkTransitionThreadCurrent<IcfgLocation>> mThreadsToForks;
	private final Set<String> mUnboundedThreads;

	public ConcurrentIcfgAnalyzer(final IIcfg<? extends LOC> icfg) {
		mIcfg = icfg;
		mUnboundedThreads = IcfgUtils.getForksInLoop(icfg).stream().map(x -> x.getNameOfForkedProcedure())
				.collect(Collectors.toSet());
		computeTopologicalOrder();
		mThreadsToForks = new HashRelation<>();
		mProceduresToForkLocations = new HashRelation<>();
		final HashRelation<String, String> forkRelation = new HashRelation<>();
		for (final var fork : getForks()) {
			final String forking = fork.getPrecedingProcedure();
			final String forked = fork.getNameOfForkedProcedure();
			mThreadsToForks.addPair(forking, fork);
			mProceduresToForkLocations.addPair(forked, (LOC) fork.getSource());
			forkRelation.addPair(forking, forked);
		}
		mThreadsToWrites = new HashRelation<>();
		mSharedWrites = new HashRelation<>();
		computeSharedWrites();
		mInterferingWrites = new HashRelation<>();
		final HashRelation<String, String> closureForks = DataStructureUtils.transitiveClosure(forkRelation);
		mTopologicalOrderPair.getFirst().forEach(x -> addInterferences(x, closureForks, Set.of()));
		// Add all writes of the remaining thread (i.e. those with loops) as interferences as an overapproximation
		final Set<ACTION> additionalInterferences = mTopologicalOrderPair.getSecond().stream()
				.flatMap(x -> mThreadsToWrites.getImage(x).stream()).collect(Collectors.toSet());
		mTopologicalOrderPair.getSecond().forEach(x -> addInterferences(x, closureForks, additionalInterferences));
	}

	private void addInterferences(final String thread, final HashRelation<String, String> closureForks,
			final Set<ACTION> additionalInterferences) {
		// Add all interferences from each fork location and additoinalInterferences (needed for a cyclc fork relation)
		final Set<ACTION> initialInterferences = new HashSet<>(additionalInterferences);
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
				final Set<ACTION> sharedWrites = getSharedWritesAtLocation(loc, closureForks);
				locsOfForkedThread.forEach(x -> mInterferingWrites.addAllPairs(x, sharedWrites));
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

	private void computeTopologicalOrder() {
		final Map<String, Set<String>> forkRelation = getForkRelation();
		final List<String> order = new ArrayList<>();
		final Map<String, Integer> forkCounter = new HashMap<>();
		forkRelation.forEach((k, v) -> forkCounter.put(k, 0));
		getForks().forEach(
				x -> forkCounter.put(x.getNameOfForkedProcedure(), forkCounter.get(x.getNameOfForkedProcedure()) + 1));
		final HashRelation<Integer, String> numberOfIncomingForks = new HashRelation<>();
		forkRelation.forEach((k, v) -> numberOfIncomingForks.addPair(forkCounter.get(k), k));
		Set<String> noIncoming = numberOfIncomingForks.removeDomainElement(0);
		final Set<String> remaining = new HashSet<>(forkRelation.keySet());
		while (!noIncoming.isEmpty()) {
			order.addAll(noIncoming);
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
		mTopologicalOrderPair = new Pair<>(order, remaining);
		mTopologicalOrder = new ArrayList<>(order.size() + remaining.size());
		mTopologicalOrder.addAll(order);
		mTopologicalOrder.addAll(remaining);
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
		for (final Entry<String, ? extends LOC> entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			final String procedure = entry.getKey();
			new IcfgEdgeIterator(entry.getValue().getOutgoingEdges()).forEachRemaining(edge -> {
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
		// Only a IProgramNonOldVar can be a shared variable, not e.g. local variables
		if (!(var instanceof IProgramNonOldVar)) {
			return false;
		}
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
