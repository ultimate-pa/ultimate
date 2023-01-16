/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IPersistentSetChoice;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.IcfgUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.ExtendedConcurrencyInformation;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
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
 * We always include all or none of the enabled actions of a thread. The algorithm thus has to select a set of threads
 * to include in the persistent set. This is based on the notion of "conflict" between the ICFG locations. If the
 * current location of thread t1 has a conflict with the current location of thread t2, and t1 is included in the
 * persistent set, then t2 must also be included.
 *
 * We have the following types of conflicts:
 *
 * 1) Commutativity conflicts: The original idea of conflicts, based on independence. Currently only unconditional
 * independence is supported.
 *
 * 2) Compatibility conflicts: Optional. Needed to ensure the choice of persistent sets is compatible with the IDfsOrder
 * used by sleep-set reduction.
 *
 * 3) Error conflicts: Needed to ensure the computed set is a membrane (no error can be reached without executing some
 * action in the set).
 *
 * 4) Join conflicts: Needed if joins cannot be resolved uniquely (there are multiple *JoinThreadOther transitions for a
 * single *JoinThreadCurrent). The possibly joined threads have to be included in the persistent set if the future
 * joining thread is, to ensure that all *JoinThreadOther transitions are enabled when the time comes.
 *
 * 5) Fork conflicts: Needed to propagate conflicts with not-yet-started threads. The forking thread (or ancestor in the
 * fork-hierarchy between threads) represents the forked thread, i.e., is included in every persistent set that would
 * include the forked thread if it already existed.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <LOC>
 *            The type of locations in the CFG
 */
public class ThreadBasedPersistentSets<LOC extends IcfgLocation> implements IPersistentSetChoice<IcfgEdge, IPredicate> {
	private final ILogger mLogger;
	private final IIcfg<LOC> mIcfg;
	private final ExtendedConcurrencyInformation<LOC> mInfo;
	private final IIndependenceRelation<?, IcfgEdge> mIndependence;
	private final IDfsOrder<IcfgEdge, IPredicate> mOrder;
	private final Collection<? extends IcfgLocation> mErrorLocs;

	private final ThreadBasedPersistentSetStatistics mStatistics;

	// Conflict-related caches
	private final PartialRelation<IcfgLocation, IcfgLocation> mCommutativityConflicts = new PartialRelation<>();
	private final PartialRelation<String, IcfgLocation> mErrorConflicts = new PartialRelation<>();
	private final PartialRelation<IcfgLocation, String> mJoinConflicts = new PartialRelation<>();
	private final PartialRelation<IcfgLocation, String> mForkCache = new PartialRelation<>();
	private final Map<IcfgLocation, Boolean> mReachErrorCache = new HashMap<>();

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
	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<LOC> icfg,
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
	public ThreadBasedPersistentSets(final IUltimateServiceProvider services, final IIcfg<LOC> icfg,
			final IIndependenceRelation<?, IcfgEdge> independence, final IDfsOrder<IcfgEdge, IPredicate> order,
			final Collection<? extends IcfgLocation> errorLocs) {
		assert !independence.isConditional() : "Conditional independence currently not supported";

		mLogger = services.getLoggingService().getLogger(ThreadBasedPersistentSets.class);
		mIcfg = icfg;
		mInfo = new ExtendedConcurrencyInformation<>(icfg);
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

		final Set<IcfgLocation> active = Set.of(mlState.getProgramPoints());
		final Set<IcfgLocation> persistentLocs =
				pickMaximalScc(active, getActiveConflicts(mlState, active, enabledActions), enabled);
		assert persistentLocs.size() <= active.size() : "Non-active locs must not be base for persistent set";
		if (persistentLocs.containsAll(enabled)) {
			mStatistics.reportTrivialQuery();
			return null;
		}

		final Set<IcfgEdge> result = enabledActions.projectToRange(persistentLocs);
		mStatistics.reportQuery();
		if (result.isEmpty()) {
			throw new AssertionError("Non-trivial persistent set must never be empty");
		}
		return result;
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mStatistics;
	}

	@Override
	public boolean ensuresCompatibility(final IDfsOrder<IcfgEdge, IPredicate> order) {
		return order == mOrder;
	}

	/**
	 * Collect a set of locations, with one location for each thread. Running threads are represented by their current
	 * location, other threads are represented by their initial location.
	 *
	 * @param state
	 *            The current state of the program
	 * @return the described set of locations
	 */
	private Map<String, IcfgLocation> getCurrentThreadLocs(final IMLPredicate state) {
		final Map<String, IcfgLocation> threadLocs = new HashMap<>();
		for (final IcfgLocation loc : state.getProgramPoints()) {
			assert !threadLocs.containsKey(loc.getProcedure()) : "Duplicate location for same thread";
			threadLocs.put(loc.getProcedure(), loc);
		}
		final Map<String, ? extends IcfgLocation> entryNodes = mIcfg.getProcedureEntryNodes();
		for (final String thread : IcfgUtils.getAllThreadInstances(mIcfg)) {
			threadLocs.putIfAbsent(thread, entryNodes.get(thread));
		}
		return threadLocs;
	}

	private static HashRelation<IcfgLocation, IcfgEdge> getEnabledActions(final IMLPredicate state) {
		final HashRelation<IcfgLocation, IcfgEdge> enabledActions = new HashRelation<>();
		final Set<IcfgLocation> locs = Set.of(state.getProgramPoints());
		for (final IcfgLocation loc : locs) {
			for (final IcfgEdge edge : loc.getOutgoingEdges()) {
				if (IcfgUtils.isEnabled(locs, edge)) {
					enabledActions.addPair(loc, edge);
				}
			}
		}
		return enabledActions;
	}

	private <N> Set<N> pickMaximalScc(final Set<N> nodes, final ISuccessorProvider<N> edges, final Set<N> required) {
		assert !nodes.isEmpty() : "Cannot compute SCCs of empty graph";

		final var sccComp = new SccComputationNonRecursive<>(mLogger, edges, StronglyConnectedComponent<N>::new,
				nodes.size(), nodes);
		final Optional<StronglyConnectedComponent<N>> persistentScc = getLeafsWithRequired(sccComp, required).stream()
				.min(Comparator
						// heuristic: choose smallest maximal SCC
						.<StronglyConnectedComponent<N>> comparingInt(StronglyConnectedComponent::getNumberOfStates)
						// fix preference among equally large SCCs
						.thenComparing(Comparator.comparing(StronglyConnectedComponent::toString)));

		assert persistentScc.isPresent() : "There must be always at least one leaf SCC";
		return persistentScc.get().getNodes();
	}

	/**
	 * Get all SCCs that contain at least one required node, such that no (transitive) successors contains a required
	 * node.
	 */
	private <N, COMP extends StronglyConnectedComponent<N>> Set<COMP>
			getLeafsWithRequired(final SccComputationNonRecursive<N, COMP> sccComp, final Set<N> required) {
		final var compSucc = sccComp.getComponentsSuccessorsProvider();
		final Set<COMP> leafs = new HashSet<>();
		for (final COMP root : sccComp.getRootComponents()) {
			leafs.addAll(getLeafsWithRequired(compSucc, required, root));
		}
		return leafs;
	}

	private <N, COMP extends StronglyConnectedComponent<N>> Set<COMP>
			getLeafsWithRequired(final ISuccessorProvider<COMP> compSucc, final Set<N> required, final COMP comp) {
		final Set<COMP> leafs = new HashSet<>();
		final Iterator<COMP> it = compSucc.getSuccessors(comp);
		while (it.hasNext()) {
			leafs.addAll(getLeafsWithRequired(compSucc, required, it.next()));
		}
		if (leafs.isEmpty() && DataStructureUtils.haveNonEmptyIntersection(comp.getNodes(), required)) {
			leafs.add(comp);
		}
		return leafs;
	}

	private ISuccessorProvider<IcfgLocation> getActiveConflicts(final IMLPredicate state,
			final Set<IcfgLocation> active, final HashRelation<IcfgLocation, IcfgEdge> enabledActions) {
		final HashRelation<IcfgLocation, IcfgLocation> conflictRelation = computeAllConflicts(state, enabledActions);
		return loc -> {
			assert active.contains(loc) : "Only conflicts between active locations should be considered";
			return conflictRelation.getImage(loc).stream().filter(active::contains).iterator();
		};
	}

	private HashRelation<IcfgLocation, IcfgLocation> computeAllConflicts(final IMLPredicate state,
			final HashRelation<IcfgLocation, IcfgEdge> enabledActions) {
		final Map<String, IcfgLocation> threadLocs = getCurrentThreadLocs(state);
		final HashRelation<IcfgLocation, IcfgLocation> conflictRelation =
				getDirectConflicts(state, threadLocs.values(), enabledActions);
		saturateForkConflicts(conflictRelation, threadLocs.values());
		return conflictRelation;
	}

	private HashRelation<IcfgLocation, IcfgLocation> getDirectConflicts(final IMLPredicate state,
			final Collection<IcfgLocation> locations, final HashRelation<IcfgLocation, IcfgEdge> enabledActions) {
		final HashRelation<IcfgLocation, IcfgLocation> result = new HashRelation<>();
		collectCompatibilityConflicts(state, enabledActions, result);

		for (final IcfgLocation persistentLoc : locations) {
			for (final IcfgLocation otherLoc : locations) {
				if (hasCommutativityConflict(persistentLoc, otherLoc) || hasErrorConflict(persistentLoc, otherLoc)
						|| hasJoinConflict(persistentLoc, otherLoc)) {
					result.addPair(persistentLoc, otherLoc);
				}
			}
		}
		return result;
	}

	private void saturateForkConflicts(final HashRelation<IcfgLocation, IcfgLocation> conflictRelation,
			final Collection<IcfgLocation> locs) {
		boolean changes;
		do {
			final HashRelation<IcfgLocation, IcfgLocation> newConflicts = new HashRelation<>();
			for (final Map.Entry<IcfgLocation, IcfgLocation> entry : conflictRelation) {
				final Collection<IcfgLocation> propagatedConflicts =
						propagateConflict(entry.getKey(), entry.getValue(), conflictRelation, locs);
				newConflicts.addAllPairs(entry.getKey(), propagatedConflicts);
			}
			changes = conflictRelation.addAll(newConflicts);
		} while (changes);
	}

	private Collection<IcfgLocation> propagateConflict(final IcfgLocation persistentLoc, final IcfgLocation otherLoc,
			final HashRelation<IcfgLocation, IcfgLocation> conflictRelation, final Collection<IcfgLocation> locs) {
		final Set<IcfgLocation> newConflicts = new HashSet<>();
		for (final IcfgLocation forkerLoc : locs) {
			if (conflictRelation.containsPair(persistentLoc, forkerLoc)) {
				continue;
			}
			if (canFork(forkerLoc, otherLoc.getProcedure())) {
				newConflicts.add(forkerLoc);
			}
		}
		return newConflicts;
	}

	private void collectCompatibilityConflicts(final IPredicate state,
			final HashRelation<IcfgLocation, IcfgEdge> enabledActions,
			final HashRelation<IcfgLocation, IcfgLocation> conflicts) {
		if (mOrder == null) {
			return;
		}

		final Comparator<IcfgEdge> order = mOrder.getOrder(state);
		final ArrayList<IcfgEdge> list = new ArrayList<>();
		for (final Map.Entry<?, HashSet<IcfgEdge>> entry : enabledActions.entrySet()) {
			list.addAll(entry.getValue());
		}
		list.sort(order);

		for (int i = 0; i < list.size() - 1; ++i) {
			final IcfgLocation first = list.get(i).getSource();
			final IcfgLocation second = list.get(i + 1).getSource();
			if (first != second) {
				conflicts.addPair(second, first);
			}
		}
	}

	private boolean hasCommutativityConflict(final IcfgLocation persistentLoc, final IcfgLocation sourceLoc) {
		if (persistentLoc == sourceLoc) {
			return false;
		}
		final String persistentThread = persistentLoc.getProcedure();
		return canReachConflict(persistentLoc, sourceLoc,
				// TODO (optimization) filter persistentLoc.getOutgoingEdges(): only enabled; or: no join / no fork ?
				e -> persistentLoc.getOutgoingEdges().stream().anyMatch(
						persAction -> mIndependence.isIndependent(null, e, persAction) != Dependence.INDEPENDENT),
				e -> !ExtendedConcurrencyInformation.isThreadLocal(e) || mInfo.mustBeJoinOf(persistentThread, e),
				mCommutativityConflicts);
	}

	/**
	 * Determines if the given locations have a "join conflict".
	 *
	 * Locations (l1, l2) have a join conflict if from l1, it is possible to reach (within the thread) a JoinCurrent
	 * transition that may correspond to a JoinOther transition belonging to the thread of l2.
	 *
	 * We ignore JoinCurrent transitions from whose target location no error location can be reached.
	 */
	private boolean hasJoinConflict(final IcfgLocation persistentLoc, final IcfgLocation otherLoc) {
		final String joinedThread = otherLoc.getProcedure();
		if (joinedThread.equals(persistentLoc.getProcedure())) {
			return false;
		}
		// Note: A previous version did not consider edges to be conflicting if they necessarily had to join
		// "joinedThread". This was however unsound on programs where the *JoinCurrent edge was in a thread that had a
		// commutativity conflict with another thread: As the thread blocked on the join and no join conflict was found,
		// the commutativity conflict was ignored.
		return IcfgUtils.canReachCached(persistentLoc,
				e -> mInfo.mayBeJoinOf(joinedThread, e) && canReachError(persistentLoc.getProcedure(), e.getTarget()),
				e -> !ExtendedConcurrencyInformation.isThreadLocal(e), l -> mJoinConflicts.contains(l, joinedThread),
				(l, r) -> mJoinConflicts.set(l, joinedThread, r));
	}

	private boolean canReachError(final String thread /* should be set of all threads */, final IcfgLocation loc) {
		return IcfgUtils.canReachCached(loc, e -> mErrorLocs.contains(e.getTarget()), e -> false, l -> {
			final Boolean stored = mReachErrorCache.get(l);
			if (stored != null) {
				return stored ? LBool.SAT : LBool.UNSAT;
			}
			// mErrorConflicts stores a more restricted notion of reachability.
			// We can reuse it if already guarantees reachability, but not if it claims unreachability.
			final LBool other = mErrorConflicts.contains(thread, l);
			return other == LBool.SAT ? LBool.SAT : LBool.UNKNOWN;
		}, (l, r) -> mReachErrorCache.put(l, r));

	}

	private boolean hasErrorConflict(final IcfgLocation persistentLoc, final IcfgLocation sourceLoc) {
		final String persistentThread = persistentLoc.getProcedure();
		if (persistentThread.equals(sourceLoc.getProcedure())) {
			return false;
		}
		return canReachConflict(persistentThread, sourceLoc, e -> mErrorLocs.contains(e.getTarget()),
				e -> !ExtendedConcurrencyInformation.isThreadLocal(e) || mInfo.mustBeJoinOf(persistentThread, e),
				mErrorConflicts);
	}

	private static <X> boolean canReachConflict(final X conflictElement, final IcfgLocation sourceLoc,
			final Predicate<IcfgEdge> isConflict, final Predicate<IcfgEdge> prune,
			final PartialRelation<X, IcfgLocation> conflictCache) {
		return IcfgUtils.canReachCached(sourceLoc, isConflict, prune, l -> conflictCache.contains(conflictElement, l),
				(x, l) -> conflictCache.set(conflictElement, x, l));
	}

	private boolean canFork(final IcfgLocation source, final String forkedThread) {
		return IcfgUtils.canReachCached(source, e -> mInfo.mayBeForkOf(forkedThread, e),
				e -> !ExtendedConcurrencyInformation.isThreadLocal(e), l -> mForkCache.contains(l, forkedThread),
				(l, r) -> mForkCache.set(l, forkedThread, r));
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

	private static class PartialRelation<X, Y> {
		private final Map<X, Map<Y, Boolean>> mRelation = new HashMap<>();

		private LBool contains(final X x, final Y y) {
			final Map<Y, Boolean> ys = mRelation.get(x);
			if (ys == null) {
				return LBool.UNKNOWN;
			}

			final Boolean elem = ys.get(y);
			if (elem == null) {
				return LBool.UNKNOWN;
			}
			return elem ? LBool.SAT : LBool.UNSAT;
		}

		private void set(final X x, final Y y, final boolean elem) {
			mRelation.computeIfAbsent(x, z -> new HashMap<>()).put(y, elem);
		}
	}
}
