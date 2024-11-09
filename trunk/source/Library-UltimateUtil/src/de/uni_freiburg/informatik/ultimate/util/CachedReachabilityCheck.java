/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE Util Library.
 *
 * The ULTIMATE Util Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Util Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Util Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Util Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Util Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.function.BiConsumer;
import java.util.function.BiPredicate;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class CachedReachabilityCheck<V, E> {

	private final Function<V, List<Pair<E, V>>> mGetOutgoing;
	private final BiPredicate<E, V> mIsTarget;
	private final BiPredicate<E, V> mPrune;

	private final Function<V, Boolean> mGetCachedResult;
	private final BiConsumer<V, Boolean> mSetCachedResult;

	public CachedReachabilityCheck(final Function<V, List<Pair<E, V>>> getOutgoing, final BiPredicate<E, V> isTarget,
			final BiPredicate<E, V> prune) {
		mGetOutgoing = getOutgoing;
		mIsTarget = isTarget;
		mPrune = prune;

		final HashMap<V, Boolean> cache = new HashMap<>();
		mGetCachedResult = cache::get;
		mSetCachedResult = cache::put;
	}

	public CachedReachabilityCheck(final Function<V, List<Pair<E, V>>> getOutgoing, final BiPredicate<E, V> isTarget,
			final BiPredicate<E, V> prune, final Function<V, Boolean> getCachedResult /* may return null */,
			final BiConsumer<V, Boolean> setCachedResult) {
		mGetOutgoing = getOutgoing;
		mIsTarget = isTarget;
		mPrune = prune;
		mGetCachedResult = getCachedResult;
		mSetCachedResult = setCachedResult;
	}

	public boolean check(final V sourceLoc) {
		// First check if result is cached.
		final Boolean cachedCanReach = mGetCachedResult.apply(sourceLoc);
		if (cachedCanReach != null) {
			return cachedCanReach;
		}

		// Do a DFS search of the CFG.
		final DfsBookkeeping<V> dfs = new DfsBookkeeping<>();
		final LinkedList<V> worklist = new LinkedList<>();

		worklist.add(sourceLoc);
		Boolean canReach = false;

		while (!worklist.isEmpty() && canReach != true) {
			final V currentLoc = worklist.getLast();

			// If the result is cached, retrieve it, mark the location as visited, and backtrack.
			final Boolean knownCanReach = mGetCachedResult.apply(currentLoc);
			if (knownCanReach != null) {
				// Do not replace UNKNOWN by UNSAT, as we must not propagate this unreachability to predecessors.
				canReach = knownCanReach || canReach != null ? knownCanReach : canReach;

				worklist.removeLast();
				dfs.push(currentLoc);
				dfs.backtrack();
				continue;
			}

			// When backtracking, remember the computed result for future queries.
			if (dfs.isVisited(currentLoc)) {
				assert canReach != true : "After reachability confirmed, should be fast-backtracking";
				worklist.removeLast();

				if (dfs.peek() != currentLoc) {
					// Node might have been added to worklist multiple times and since been visited. Hence it might not
					// be on the stack. In that case, no backtracking is needed, nor do we visit the node again.
					continue;
				}

				final boolean completeBacktrack = dfs.backtrack();
				// Inside a loop, reachability cannot be UNSAT. Yet, a successor outside the loop might have
				// UNSAT status. Once back inside the loop, we here set canReach to UNKNOWN.
				// Conversely, if we just backtracked the outermost loop head, reset canReach to UNSAT.
				canReach = completeBacktrack ? false : null;

				if (canReach != null) {
					assert canReach == false;
					mSetCachedResult.accept(currentLoc, false);
				}
				continue;
			}

			// Visit location.
			dfs.push(currentLoc);

			final List<Pair<E, V>> outgoing = mGetOutgoing.apply(currentLoc); // currentLoc.getOutgoingEdges();
			final List<V> successors = new ArrayList<>(outgoing.size());
			for (final Pair<E, V> edge : outgoing) {
				final V succ = edge.getSecond();

				// Abort when reachability is confirmed.
				if (mIsTarget.test(edge.getFirst(), edge.getSecond())) {
					canReach = true;
					break;
				}

				// Ignore successors of explicitly pruned edges.
				if (mPrune.test(edge.getFirst(), edge.getSecond())) {
					continue;
				}

				final int stackIndex;
				if (!dfs.isVisited(succ)) {
					// If the successor has not been visited before, explore it now.
					successors.add(succ);
				} else if ((stackIndex = dfs.stackIndexOf(succ)) != -1) {
					// If the edge leads back to the stack, reachability is unknown until succ (or an even earlier loop
					// head) is backtracked. To avoid infinite looping, we do not explore succ.
					assert mGetCachedResult.apply(succ) == null : "Loop heads on stack must have UNKNOWN status";
					canReach = null;
					dfs.updateLoopHead(currentLoc, new Pair<>(stackIndex, succ));
				} else {
					// If the successor has been visited before, but is not on the stack, then we know its reachability
					// is either UNSAT or UNKNOWN.
					final Boolean succCanReach = mGetCachedResult.apply(succ);
					assert succCanReach != true : "Backtracked node must not have SAT status";

					// In either case, we do not need to explore it again. Instead, we simply propagate reachability and
					// loop head information back to currentLoc.
					canReach = succCanReach == null ? null : canReach;
					dfs.backPropagateLoopHead(currentLoc, succ);
				}
			}

			// When reachability was confirmed, do not search any further.
			if (canReach != true) {
				successors.stream().forEach(worklist::add);
			}
		}

		// Fast-backtrack if necessary
		assert dfs.isStackEmpty() || canReach == true : "Fast-backtracking must only happen in case of reachability";
		fastBacktrack(dfs);

		assert checkResultConsistency(sourceLoc, canReach);
		return canReach == true;
	}

	// Fast-backtrack: If we exited the search because reachability was confirmed, we only backtrack,
	// and no longer explore states on the work list.
	private void fastBacktrack(final DfsBookkeeping<V> dfs) {
		while (!dfs.isStackEmpty()) {
			final V currentLoc = dfs.peek();
			dfs.backtrack();
			mSetCachedResult.accept(currentLoc, true);
		}
	}

	private boolean checkResultConsistency(final V sourceLoc, final Boolean result) {
		final Boolean cachedReachability = mGetCachedResult.apply(sourceLoc);
		assert cachedReachability != null : "reachability should be clearly determined";
		assert cachedReachability == result : "contradictory reachability: " + cachedReachability + " != " + result;
		return true;
	}
}
