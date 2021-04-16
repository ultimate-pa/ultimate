/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Arrays;
import java.util.Iterator;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputationNonRecursive;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;

/**
 * A choice of persistent sets for pthread-like concurrent programs. By analysing the CFG, we compute persistent sets
 * for the concurrent product in polynomial time (in the size of the CFG).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ThreadBasedPersistentSets implements IPersistentSetChoice<IcfgEdge, IPredicate> {
	private final ILogger mLogger;
	private final ExtendedConcurrencyInformation mInfo;
	private final IIndependenceRelation<?, IcfgEdge> mIndependence;

	private final HashRelation<IcfgLocation, IcfgLocation> mCommutativityConflict = new HashRelation<>();
	private final HashRelation<IcfgLocation, IcfgLocation> mNoCommutativityConflict = new HashRelation<>();

	// TODO move this to statistics
	private int mQueries;
	private int mTrivialQueries;
	private long mComputationTime;

	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final IIndependenceRelation<?, IcfgEdge> independence) {
		assert !independence.isConditional() : "Conditional independence currently not supported";

		mLogger = services.getLoggingService().getLogger(ThreadBasedPersistentSets.class);
		mInfo = new ExtendedConcurrencyInformation(icfg);
		mIndependence = independence;
	}

	@Override
	public Set<IcfgEdge> persistentSet(final IPredicate state) {
		boolean isTrivial = false;
		final long start = System.currentTimeMillis();
		try {
			final IMLPredicate mlState = (IMLPredicate) state;
			final Set<IcfgLocation> locs = Set.of(mlState.getProgramPoints());
			final Set<IcfgLocation> enabled = Arrays.stream(mlState.getProgramPoints())
					.filter(l -> l.getOutgoingEdges().stream().anyMatch(e -> isEnabled(locs, e)))
					.collect(Collectors.toSet());

			// For non-concurrent parts of a program, no need for complicated computations.
			if (enabled.size() <= 1) {
				isTrivial = true;
				return null;
			}

			final var sccComp = new SccComputationNonRecursive<>(mLogger, l -> getConflicts(enabled, l).iterator(),
					StronglyConnectedComponent<IcfgLocation>::new, enabled.size(), enabled);
			final var persistentCandidates = sccComp.getRootComponents();
			// TODO possibly use heuristics in selection, e.g. size or IDfsOrder
			final Set<IcfgLocation> persistentLocs = persistentCandidates.iterator().next().getNodes();

			assert persistentLocs.size() <= enabled.size() : "Non-enabled locs must not be base for persistent set";
			if (persistentLocs.size() >= enabled.size()) {
				isTrivial = true;
				return null;
			}

			return persistentLocs.stream().flatMap(l -> l.getOutgoingEdges().stream()).collect(Collectors.toSet());
		} finally {
			// TODO move this to statistics: beginQuery(), reportQuery(boolean isTrivial)
			mQueries++;
			if (isTrivial) {
				mTrivialQueries++;
			}
			mComputationTime += System.currentTimeMillis() - start;
			if (mQueries % 20_000 == 0) {
				mLogger.warn("Computed %d persistent sets (%.2f %% trivial) in %d s", mQueries,
						(100.0 * mTrivialQueries) / mQueries, mComputationTime / 1000);
			}
		}
	}

	private boolean isEnabled(final Set<IcfgLocation> locs, final IcfgEdge edge) {
		if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
			final var joinOther = (IIcfgJoinTransitionThreadOther<?>) edge;
			final var joinCurrent = joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread();
			return locs.contains(joinOther.getSource()) && locs.contains(joinCurrent.getSource());
		}
		if (edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			final var joinCurrent = (IIcfgJoinTransitionThreadCurrent<IcfgLocation>) edge;
			final var joinOther = mInfo.getJoinOther(joinCurrent);
			return locs.contains(joinOther.getSource()) && locs.contains(joinCurrent.getSource());
		}
		return locs.contains(edge.getSource());
	}

	private Stream<IcfgLocation> getConflicts(final Set<IcfgLocation> enabled, final IcfgLocation loc) {
		// TODO support enforcing compliance for thread-uniform DFS orders
		// TODO Re-use (more) dependence information across states (?)
		return Stream.concat(getJoinConflicts(enabled, loc.getProcedure()), getCommutativityConflicts(enabled, loc));
	}

	private Stream<IcfgLocation> getJoinConflicts(final Set<IcfgLocation> enabled, final String joinedThread) {
		// TODO (optimization:) except if joins are already enabled in state
		return enabled.stream().filter(l -> canJoinLater(l, joinedThread));
	}

	private boolean canJoinLater(final IcfgLocation joinerLoc, final String joinedThread) {
		// TODO Is there some easy way to prune incorrect joins from CFG?
		return !mInfo.getReachableJoinsOf(joinerLoc, joinedThread).isEmpty();
	}

	private Stream<IcfgLocation> getCommutativityConflicts(final Set<IcfgLocation> enabled, final IcfgLocation loc) {
		return enabled.stream().filter(l -> hasCommutativityConflict(loc, l));
	}

	private boolean hasCommutativityConflict(final IcfgLocation loc, final IcfgLocation l) {
		if (mCommutativityConflict.containsPair(loc, l)) {
			return true;
		}
		if (mNoCommutativityConflict.containsPair(loc, l)) {
			return false;
		}
		return computeCommutativityConflict(loc, l);
	}

	private boolean computeCommutativityConflict(final IcfgLocation loc1, final IcfgLocation loc2) {
		// TODO optimize: if loc2 -> loc2' and loc2' has a conflict, then so has loc2

		final Iterator<IcfgEdge> iterator = new IcfgEdgeIterator(loc2, ThreadBasedPersistentSets::isThreadLocal);
		while (iterator.hasNext()) {
			final IcfgEdge other = iterator.next();
			for (final IcfgEdge action : loc1.getOutgoingEdges()) {
				if (!mIndependence.contains(null, other, action)) {
					mCommutativityConflict.addPair(loc1, loc2);
					return true;
				}
			}
		}
		mNoCommutativityConflict.addPair(loc1, loc2);
		return false;
	}

	private static boolean isThreadLocal(final IcfgEdge edge) {
		return !(edge instanceof IIcfgForkTransitionThreadOther<?>)
				&& !(edge instanceof IIcfgJoinTransitionThreadOther<?>);
	}
}
