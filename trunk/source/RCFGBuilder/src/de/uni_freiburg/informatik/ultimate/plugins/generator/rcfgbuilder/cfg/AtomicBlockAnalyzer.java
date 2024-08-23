/*
 * Copyright (C) 2024 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2024 University of Freiburg
 *
 * This file is part of the ULTIMATE RCFGBuilder plug-in.
 *
 * The ULTIMATE RCFGBuilder plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE RCFGBuilder plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE RCFGBuilder plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE RCFGBuilder plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE RCFGBuilder plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg;

import java.util.ArrayDeque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * A helper class to deal with atomic blocks (marked via {@link AtomicBlockInfo}) in
 * {@link CfgBuilder.LargeBlockEncoding}).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
class AtomicBlockAnalyzer {
	private final BoogieIcfgContainer mIcfg;

	// Locations that are (strictly) inside an atomic block.
	private final Set<BoogieIcfgLocation> mAtomicPoints;

	// Locations that are the starting point for an atomic block.
	// Note that there may be several outgoing edges, and not all of them necessarily belong to an atomic block.
	private final Set<BoogieIcfgLocation> mAtomicBegins;

	// Locations that are the end point for an atomic block.
	// Note that there may be several incoming edges, and not all of them necessarily belong to an atomic block.
	private final Set<BoogieIcfgLocation> mAtomicEnds;

	public AtomicBlockAnalyzer(final BoogieIcfgContainer icfg) {
		mIcfg = icfg;

		// collect locations inside atomic blocks
		mAtomicPoints = collectAtomicPoints();
		assert getAllLocations().allMatch(pp -> !mAtomicPoints.contains(pp)
				|| allPredecessorsAtomic(pp)) : "Atomic point with unexpected non-atomic predecessor!";
		assert getAllLocations().allMatch(pp -> !mAtomicPoints.contains(pp)
				|| allSuccessorsAtomic(pp)) : "Atomic point with unexpected non-atomic successor!";

		// collect locations at boundaries of atomic blocks
		mAtomicBegins =
				getAllLocations()
						.filter(loc -> !mAtomicPoints.contains(loc) && loc.getOutgoingEdges().stream()
								.anyMatch(e -> AtomicBlockInfo.isStartOfAtomicBlock(e)
										|| AtomicBlockInfo.isCompleteAtomicBlock(e)))
						.collect(Collectors.toCollection(HashSet::new));
		mAtomicEnds = getAllLocations()
				.filter(loc -> !mAtomicPoints.contains(loc) && loc.getIncomingEdges().stream().anyMatch(
						e -> AtomicBlockInfo.isEndOfAtomicBlock(e) || AtomicBlockInfo.isCompleteAtomicBlock(e)))
				.collect(Collectors.toCollection(HashSet::new));
	}

	public boolean isInsideAtomicBlock(final BoogieIcfgLocation pp) {
		final boolean isInAtomicBlock = mAtomicPoints.contains(pp);
		if (isInAtomicBlock) {
			assert allPredecessorsAtomic(pp) : "Atomic point " + pp + " has non-atomic predecessors";
			assert allSuccessorsAtomic(pp) : "Atomic point " + pp + " has non-atomic successors";
		}
		return isInAtomicBlock;
	}

	public boolean isAtomicBoundary(final BoogieIcfgLocation loc) {
		return isAtomicBegin(loc) || isAtomicEnd(loc);
	}

	public boolean isAtomicBegin(final BoogieIcfgLocation loc) {
		return mAtomicBegins.contains(loc);
	}

	public boolean isAtomicEnd(final BoogieIcfgLocation loc) {
		return mAtomicEnds.contains(loc);
	}

	public void removeLocation(final BoogieIcfgLocation pp) {
		mAtomicPoints.remove(pp);
		mAtomicBegins.remove(pp);
		mAtomicEnds.remove(pp);
	}

	public static void ensureAtomicCompositionIsComplete(final BoogieIcfgContainer icfg, final ILogger logger) {
		final Iterable<IcfgEdge> edges = getAllEdges(icfg)::iterator;
		for (final var edge : edges) {
			ensureAtomicCompositionComplete(edge, logger);
		}
	}

	private static void ensureAtomicCompositionComplete(final IcfgEdge edge, final ILogger logger) {
		if (AtomicBlockInfo.isEndOfAtomicBlock(edge)) {
			// We must never have any dangling ends of atomic blocks;
			// such an edge should have been fused with the corresponding start of the atomic block.
			throw new UnsupportedOperationException("Incomplete atomic composition (dangling end of atomic block: "
					+ edge + "). Is there illegal control flow (e.g. loops) within an atomic block?");
		}

		// If the edge is neither the start nor the end of an atomic block, everything is fine.
		if (!AtomicBlockInfo.isStartOfAtomicBlock(edge)) {
			// Edge may be marked as complete atomic block.
			// If so, remove the annotation as it is only for internal use.
			AtomicBlockInfo.removeAnnotation(edge);
			return;
		}

		final var successor = (BoogieIcfgLocation) edge.getTarget();
		if (successor.isErrorLocation()) {
			// Assert statements in atomic blocks are ok.
			// Remove the annotation as it is only for internal use.
			AtomicBlockInfo.removeAnnotation(edge);
			return;
		}

		// We tolerate nodes without successors inside atomic blocks, such as thread exit locations.
		final boolean successorIsSink = successor.getOutgoingEdges().isEmpty();
		if (!successorIsSink) {
			throw new UnsupportedOperationException("Incomplete atomic composition (dangling start of atomic block: "
					+ edge + "). Is there illegal control flow (e.g. loops) within an atomic block?");
		}
		logger.warn("Unexpected successor node of atomic block begin: %s is not an error location.", successor);

		// Remove the annotation as it is only for internal use.
		AtomicBlockInfo.removeAnnotation(edge);
	}

	private static Stream<IcfgEdge> getAllEdges(final BoogieIcfgContainer icfg) {
		return IcfgUtils.getAllLocations(icfg).flatMap(loc -> loc.getOutgoingEdges().stream()).distinct();
	}

	private Stream<BoogieIcfgLocation> getAllLocations() {
		return IcfgUtils.getAllLocations(mIcfg);
	}

	private Stream<IcfgEdge> getAllEdges() {
		return getAllLocations().flatMap(loc -> loc.getOutgoingEdges().stream()).distinct();
	}

	/**
	 * Identifies all nodes that are inside an atomic block.
	 */
	private Set<BoogieIcfgLocation> collectAtomicPoints() {
		final var atomicPoints = new HashSet<BoogieIcfgLocation>();
		final ArrayDeque<Pair<IcfgEdge, Integer>> worklist = new ArrayDeque<>();
		final Map<BoogieIcfgLocation, Integer> visited = new HashMap<>();

		// Begin at start edges of atomic blocks
		getAllEdges().filter(AtomicBlockInfo::isStartOfAtomicBlock).forEach(e -> worklist.add(new Pair<>(e, 0)));

		while (!worklist.isEmpty()) {
			final var entry = worklist.poll();
			final IcfgEdge edge = entry.getFirst();
			final int level = entry.getSecond();

			final BoogieIcfgLocation pp = (BoogieIcfgLocation) edge.getTarget();
			int newLevel;
			if (AtomicBlockInfo.isEndOfAtomicBlock(edge)) {
				newLevel = level - 1;
			} else if (AtomicBlockInfo.isStartOfAtomicBlock(edge)) {
				newLevel = level + 1;
			} else {
				newLevel = level;
			}
			if (newLevel == 0) {
				continue;
			}

			atomicPoints.add(pp);
			final int visitedLevel = visited.getOrDefault(pp, 0);
			if (visitedLevel < newLevel) {
				visited.put(pp, newLevel);
				for (final IcfgEdge next : pp.getOutgoingEdges()) {
					worklist.add(new Pair<>(next, newLevel));
				}
			}
		}

		return atomicPoints;
	}

	private boolean allPredecessorsAtomic(final BoogieIcfgLocation pp) {
		return pp.getIncomingEdges().stream().allMatch(
				edge -> mAtomicPoints.contains(edge.getSource()) || AtomicBlockInfo.isStartOfAtomicBlock(edge));
	}

	private boolean allSuccessorsAtomic(final BoogieIcfgLocation pp) {
		return pp.getOutgoingEdges().stream()
				.allMatch(edge -> mAtomicPoints.contains(edge.getTarget()) || AtomicBlockInfo.isEndOfAtomicBlock(edge));
	}
}
