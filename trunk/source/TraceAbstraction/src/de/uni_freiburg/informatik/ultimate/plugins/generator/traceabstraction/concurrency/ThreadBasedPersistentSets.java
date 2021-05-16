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

import java.util.Collection;
import java.util.Comparator;
import java.util.Iterator;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgDominatorInfo;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgForkTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgJoinTransitionThreadOther;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputation.ISuccessorProvider;
import de.uni_freiburg.informatik.ultimate.util.scc.SccComputationNonRecursive;
import de.uni_freiburg.informatik.ultimate.util.scc.StronglyConnectedComponent;
import de.uni_freiburg.informatik.ultimate.util.statistics.AbstractStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;
import de.uni_freiburg.informatik.ultimate.util.statistics.KeyType;

/**
 * A choice of persistent sets for pthread-like concurrent programs. By analysing the CFG, we compute persistent sets
 * for the concurrent product in polynomial time (in the size of the CFG).
 *
 * Note that this is currently unsound if either (i) the analysed programs has insufficient thread instances (through
 * the fault of persistent set reduction, that fact might be missed), or (ii) the analysed programs has assertions that
 * can be reached while other threads are still running (i.e. it is really mostly intended for postcondition checking).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ThreadBasedPersistentSets implements IPersistentSetChoice<IcfgEdge, IPredicate> {
	private final ILogger mLogger;
	private final ExtendedConcurrencyInformation mInfo;
	private final IcfgDominatorInfo<?> mDominatorInfo;
	private final IIndependenceRelation<?, IcfgEdge> mIndependence;
	private final IDfsOrder<IcfgEdge, IPredicate> mOrder;
	private final Collection<? extends IcfgLocation> mErrorLocs;

	private final HashRelation<IcfgLocation, IcfgLocation> mCommutativityConflict = new HashRelation<>();
	private final HashRelation<IcfgLocation, IcfgLocation> mNoCommutativityConflict = new HashRelation<>();

	private final ThreadBasedPersistentSetStatistics mStatistics;

	/**
	 * Create a new instance for a given CFG.
	 *
	 * @param services
	 *            Ultimate services, used for logging
	 * @param icfg
	 *            An {@link IIcfg} based on which persistent sets will be computed
	 * @param independence
	 *            An unconditional independence relation which is used to compute persistent sets
	 */
	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final IIndependenceRelation<?, IcfgEdge> independence) {
		this(services, icfg, independence, null, null);
	}

	/**
	 * Create a new instance for a given CFG, and (optionally) enforce compatibility with a given DFS order.
	 *
	 * @param services
	 *            Ultimate services, used for logging
	 * @param icfg
	 *            An {@link IIcfg} based on which persistent sets will be computed
	 * @param independence
	 *            An unconditional independence relation which is used to compute persistent sets
	 * @param order
	 *            A DFS traversal order with which the persistent sets should be compatible. Set this to null if
	 *            compatibility should not be enforced.
	 * @param errorLocs
	 *            The set of error locations to be considered. If null, all error locations of the CFG are used.
	 */
	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<?> icfg,
			final IIndependenceRelation<?, IcfgEdge> independence, final IDfsOrder<IcfgEdge, IPredicate> order,
			final Collection<? extends IcfgLocation> errorLocs) {
		assert !independence.isConditional() : "Conditional independence currently not supported";

		mLogger = services.getLoggingService().getLogger(ThreadBasedPersistentSets.class);
		mInfo = new ExtendedConcurrencyInformation(icfg);
		mDominatorInfo = new IcfgDominatorInfo<>(icfg);
		mIndependence = independence;
		mOrder = order;
		mErrorLocs = errorLocs == null ? IcfgUtils.getErrorLocations(icfg) : errorLocs;
		mStatistics = new ThreadBasedPersistentSetStatistics(independence);
	}

	@Override
	public Set<IcfgEdge> persistentSet(final IPredicate state) {
		mStatistics.beginComputation();

		final IMLPredicate mlState = (IMLPredicate) state;
		final HashRelation<IcfgLocation, IcfgEdge> enabledActions = getEnabledActions(mlState);
		final Set<IcfgLocation> enabled = enabledActions.getDomain();

		// For non-concurrent parts of a program, no need for complicated computations.
		if (enabled.size() <= 1) {
			mStatistics.reportTrivialQuery();
			return null;
		}

		final Set<IcfgLocation> persistentLocs = pickMaximalScc(enabled, l -> getConflicts(mlState, enabledActions, l));
		assert persistentLocs.size() <= enabled.size() : "Non-enabled locs must not be base for persistent set";
		if (persistentLocs.size() >= enabled.size()) {
			mStatistics.reportTrivialQuery();
			return null;
		}

		final Set<IcfgEdge> result = enabledActions.projectToRange(persistentLocs);
		mStatistics.reportQuery();
		return result;
	}

	private <N> Set<N> pickMaximalScc(final Set<N> nodes, final ISuccessorProvider<N> edges) {
		assert !nodes.isEmpty() : "Cannot compute SCCs of empty graph";

		final var sccComp = new SccComputationNonRecursive<>(mLogger, edges, StronglyConnectedComponent<N>::new,
				nodes.size(), nodes);
		// heuristic: choose smallest maximal SCC
		final Optional<StronglyConnectedComponent<N>> persistentScc = sccComp.getLeafComponents().stream()
				.min(Comparator.comparingInt(StronglyConnectedComponent::getNumberOfStates));

		assert persistentScc.isPresent() : "There must be always at least one leaf SCC";
		return persistentScc.get().getNodes();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	private static HashRelation<IcfgLocation, IcfgEdge> getEnabledActions(final IMLPredicate state) {
		final HashRelation<IcfgLocation, IcfgEdge> enabledActions = new HashRelation<>();
		final Set<IcfgLocation> locs = Set.of(state.getProgramPoints());
		for (final IcfgLocation loc : locs) {
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				if (isEnabled(locs, edge)) {
					enabledActions.addPair(loc, edge);
				}
			}
		}
		return enabledActions;
	}

	private static boolean isEnabled(final Set<IcfgLocation> locs, final IcfgEdge edge) {
		if (edge instanceof IIcfgForkTransitionThreadCurrent<?>
				|| edge instanceof IIcfgJoinTransitionThreadCurrent<?>) {
			// These edges exist in the Icfg, but in traces they are represented by the respective
			// IIcfg*TransitionThreadOther transitions. Hence they are never enabled.
			return false;
		}
		if (edge instanceof IIcfgForkTransitionThreadOther<?>) {
			// Enabled if predecessor location is in state, and forked thread instance is not yet running.
			final Set<String> threads = locs.stream().map(IcfgLocation::getProcedure).collect(Collectors.toSet());
			final String forkedThread = edge.getSucceedingProcedure();
			return locs.contains(edge.getSource()) && !threads.contains(forkedThread);
		}
		if (edge instanceof IIcfgJoinTransitionThreadOther<?>) {
			// Enabled if predecessor location and predecessor location of the corresponding
			// IIcfg*TransitionThreadCurrent instance are both in the state.
			final var joinOther = (IIcfgJoinTransitionThreadOther<?>) edge;
			final var joinCurrent = joinOther.getCorrespondingIIcfgJoinTransitionCurrentThread();
			return locs.contains(joinOther.getSource()) && locs.contains(joinCurrent.getSource());
		}
		return locs.contains(edge.getSource());
	}

	private Iterator<IcfgLocation> getConflicts(final IPredicate state,
			final HashRelation<IcfgLocation, IcfgEdge> enabledActions, final IcfgLocation loc) {
		// TODO (optimization:) Re-use (more) dependence information across states (?)
		final Set<IcfgLocation> enabled = enabledActions.getDomain();
		return Stream
				.of(getCompatibilityConflicts(state, enabledActions, loc),
						getJoinConflicts(enabled, loc.getProcedure()), getCommutativityConflicts(enabled, loc))
				.flatMap(s -> s).iterator();
	}

	private Stream<IcfgLocation> getJoinConflicts(final Set<IcfgLocation> enabled, final String joinedThread) {
		// TODO (optimization:) except if joins are already enabled in state
		return enabled.stream().filter(l -> canJoinLater(l, joinedThread));
	}

	private boolean canJoinLater(final IcfgLocation joinerLoc, final String joinedThread) {
		// TODO (optimization:) Is there some easy way to prune incorrect joins from CFG?
		return !mInfo.getReachableJoinsOf(joinerLoc, joinedThread).isEmpty();
	}

	private Stream<IcfgLocation> getCommutativityConflicts(final Set<IcfgLocation> enabled, final IcfgLocation loc) {
		// TODO (optimization:) What if conflict is only reachable after join of thread(loc) ?
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

	private Stream<IcfgLocation> getCompatibilityConflicts(final IPredicate state,
			final HashRelation<IcfgLocation, IcfgEdge> enabledActions, final IcfgLocation loc) {
		if (mOrder == null) {
			return Stream.empty();
		}

		final Comparator<IcfgEdge> comp = mOrder.getOrder(state);
		return enabledActions.getDomain().stream().filter(other -> other != loc
				&& hasCompatibilityConflict(comp, enabledActions.getImage(loc), enabledActions.getImage(other)));
	}

	private static boolean hasCompatibilityConflict(final Comparator<IcfgEdge> comp, final Set<IcfgEdge> actions,
			final Set<IcfgEdge> otherActions) {
		for (final IcfgEdge action : actions) {
			for (final IcfgEdge other : otherActions) {
				if (comp.compare(action, other) < 0) {
					return true;
				}
			}
		}
		return false;
	}

	private static boolean isThreadLocal(final IcfgEdge edge) {
		return !(edge instanceof IIcfgForkTransitionThreadOther<?>)
				&& !(edge instanceof IIcfgJoinTransitionThreadOther<?>);
	}

	private static final class ThreadBasedPersistentSetStatistics extends AbstractStatisticsDataProvider {
		public static final String COMPUTATION_TIME = "Persistent set computation time";
		public static final String PERSISTENT_SET_COMPUTATIONS = "Number of persistent set computation";
		public static final String TRIVIAL_SETS = "Number of trivial persistent sets";
		public static final String UNDERLYING_INDEPENDENCE = "Underlying independence relation";

		private long mComputationTime;
		private int mTrivialSets;
		private int mQueries;

		private long mComputationStart = -1;

		private ThreadBasedPersistentSetStatistics(final IIndependenceRelation<?, IcfgEdge> independence) {
			declare(COMPUTATION_TIME, () -> mComputationTime, KeyType.TIMER);
			declare(PERSISTENT_SET_COMPUTATIONS, () -> mQueries, KeyType.COUNTER);
			declare(TRIVIAL_SETS, () -> mTrivialSets, KeyType.COUNTER);
			forward(UNDERLYING_INDEPENDENCE, independence::getStatistics);
		}

		private void beginComputation() {
			assert mComputationStart == -1 : "Computation timer already running";
			mComputationStart = System.nanoTime();
		}

		private void reportTrivialQuery() {
			mTrivialSets++;
			reportQuery();
		}

		private void reportQuery() {
			assert mComputationStart >= 0 : "Computation timer was not running";
			mComputationTime += System.nanoTime() - mComputationStart;
			mComputationStart = -1;
			mQueries++;
		}
	}
}
