/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 *
 */

public class FixpointEngineConcurrentUtils<STATE extends IAbstractState<STATE>, ACTION, LOC> {

	private final IIcfg<?> mIcfg;
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final HashRelation<ACTION, IProgramVarOrConst> mSharedWriteWrittenVars;
	private final Map<ACTION, Set<IProgramVarOrConst>> mSharedWriteReadVars;
	private final HashRelation<ACTION, IProgramVarOrConst> mSharedReadReadVars;
	private final Map<String, Set<String>> mDependingProcedures;
	private final Map<ACTION, Set<ACTION>> mWritesPerRead;
	private final Map<String, Set<ACTION>> mWritesPerProcedure;
	private final Map<String, Set<ACTION>> mReadsPerProcedure;
	private final HashRelation<String, ACTION> mSelfReachableReads;
	private final HashRelation<String, LOC> mForkedAt;
	private final HashRelation<String, String> mForks;
	private final HashRelation<String, ACTION> mActionsInProcedure;
	private final Set<String> mParallelProcedures;
	private final List<String> mTopologicalOrder;

	private final Map<String, Set<Map<LOC, Set<ACTION>>>> mCrossProducts;

	public FixpointEngineConcurrentUtils(final IIcfg<?> icfg, final ITransitionProvider<ACTION, LOC> transProvider) {
		mIcfg = icfg;
		mTransitionProvider = transProvider;
		mSharedWriteWrittenVars = new HashRelation<>();
		mSharedWriteReadVars = new HashMap<>();
		mSharedReadReadVars = new HashRelation<>();
		mDependingProcedures = new HashMap<>();
		mWritesPerRead = new HashMap<>();
		mWritesPerProcedure = new HashMap<>();
		mReadsPerProcedure = new HashMap<>();
		mSelfReachableReads = new HashRelation<>();
		mForkedAt = new HashRelation<>();
		mForks = new HashRelation<>();
		mActionsInProcedure = new HashRelation<>();
		mParallelProcedures = new HashSet<>();

		mCrossProducts = new HashMap<>();

		mTopologicalOrder = new ArrayList<>();

		initialize(mIcfg.getProcedureEntryNodes());
	}

	public Set<ACTION> getAllReads() {
		final Set<ACTION> result = new HashSet<>();
		for (final String procedure : mIcfg.getCfgSmtToolkit().getProcedures()) {
			final Set<ACTION> temp = getReads(procedure);
			if (temp != null) {
				result.addAll(getReads(procedure));
			}
		}
		return result;
	}

	/***
	 *
	 * @param entryNodes
	 * @return List of Relations for FeasibilityFilter regarding the Program Order.
	 *
	 *         Order in List: 1. DOMINATES 2. NOTREACHABLEFROM 3. THCREATES 4. THJOINS
	 */
	public List<HashRelation<ACTION, ACTION>>
			getProgramOrderConstraints(final Map<String, ? extends IcfgLocation> entryNodes) {
		final List<HashRelation<ACTION, ACTION>> result = new ArrayList<>();
		result.add(getDominates(entryNodes));
		result.add(getNotReachableFrom(entryNodes));
		result.add(getThCreates(entryNodes));
		result.add(getThJoins());
		return result;
	}

	/***
	 *
	 * @return DOMINATES: (x,y) in DOMINATES, iff all paths from the thread entry to y contain x.
	 */
	public HashRelation<ACTION, ACTION> getDominates(final Map<String, ? extends IcfgLocation> entryNodes) {
		final Map<ACTION, Set<ACTION>> dominatedBy = new HashMap<>();
		for (final var entry : entryNodes.entrySet()) {
			final Queue<ACTION> workList = new ArrayDeque<>();
			// initialize
			for (final var action : mTransitionProvider.getSuccessorActions((LOC) entry.getValue())) {
				workList.add(action);
				final Set<ACTION> identity = new HashSet<>();
				identity.add(action);
				dominatedBy.put(action, identity);
			}

			while (!workList.isEmpty()) {
				final ACTION item = workList.poll();
				final LOC target = mTransitionProvider.getTarget(item);
				final Set<ACTION> itemDominatedBy = dominatedBy.get(item);
				for (final var successor : mTransitionProvider.getSuccessorActions(target)) {
					// if changes -> add successor to workList
					final Set<ACTION> currentlyDominatedBy = dominatedBy.get(successor);
					if (currentlyDominatedBy == null) {
						final Set<ACTION> tempSet = new HashSet<>();
						tempSet.add(successor);
						tempSet.addAll(itemDominatedBy);
						dominatedBy.put(successor, tempSet);
						workList.add(successor);
						continue;
					}
					final Set<ACTION> intersection =
							DataStructureUtils.intersection(itemDominatedBy, currentlyDominatedBy);
					if (!intersection.equals(currentlyDominatedBy)) {
						dominatedBy.put(successor, intersection);
						workList.add(successor);
					}
				}
			}
		}
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		// reverse dominatedBy
		for (final var entry : dominatedBy.entrySet()) {
			entry.getValue().forEach(value -> result.addPair(value, entry.getKey()));
		}
		return result;
	}

	/***
	 *
	 * @return NOTREACHABLEFROM: (x,y) in NOTREACHABLEFROM, iff x is not reachable from y.
	 */
	public HashRelation<ACTION, ACTION> getNotReachableFrom(final Map<String, ? extends IcfgLocation> entryNodes) {
		// compute Set of all ACTIONS in Thread -> X
		// compute ReachableFrom via Iterator
		// Compute AllActions\ReachableFrom -> NOTREACHABLEFROM
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();

		// very inefficient, but first approach
		// TODO: find a more efficient way
		for (final var entry : entryNodes.entrySet()) {
			if (mParallelProcedures.contains(entry.getKey())) {
				// procedure can run parallel to itself -> NotReachable condition is not valid anymore
				continue;
			}
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			for (final var item : iterator.asStream().collect(Collectors.toSet())) {
				final Set<ACTION> reachable = new HashSet<>();
				final ACTION action = (ACTION) item;
				reachable.add(action);
				final IcfgEdgeIterator edgeIterator = new IcfgEdgeIterator(item);
				edgeIterator.asStream().forEach(edge -> reachable.add((ACTION) edge));
				final Set<ACTION> notReachable =
						DataStructureUtils.difference(mActionsInProcedure.getImage(entry.getKey()), reachable);
				notReachable.forEach(x -> result.addPair(x, action));
			}
		}
		return result;
	}

	/***
	 *
	 * @return Domain are thread entry actions, image is a fork which forks the corresponding thread
	 */
	public HashRelation<ACTION, ACTION> getThCreates(final Map<String, ? extends IcfgLocation> entryNodes) {
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		for (final var entry : mForkedAt.entrySet()) {
			final Set<ACTION> entryActions = new HashSet<>();
			entryNodes.get(entry.getKey()).getOutgoingEdges().forEach(edge -> entryActions.add((ACTION) edge));
			for (final var forkLocation : entry.getValue()) {
				mTransitionProvider.getSuccessorActions(forkLocation)
						.forEach(fork -> result.addAllPairs(fork, entryActions));
			}
		}
		return result;
	}

	public HashRelation<ACTION, ACTION> getThJoins() {
		// no support yet
		return new HashRelation<>();
	}

	/***
	 *
	 * @return ISLOAD: (l, v) in ISLOAD, iff l is a read of the variable v
	 */
	public HashRelation<ACTION, IProgramVarOrConst> getIsLoad() {
		return mSharedReadReadVars;
	}

	/***
	 *
	 * @return ISSTORE: (l, v) in ISSTORE, iff l is a write to the variable v
	 */
	public HashRelation<ACTION, IProgramVarOrConst> getIsStore() {
		return mSharedWriteWrittenVars;
	}

	public Set<ACTION> getIsEntry() {
		final Set<ACTION> result = new HashSet<>();
		final String initialProcedure = mTopologicalOrder.get(0);
		for (final var entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			if (!entry.getKey().equals(initialProcedure)) {
				result.addAll(mTransitionProvider.getSuccessorActions((LOC) entry.getValue()));
			}
		}
		return result;
	}

	public Set<ACTION> getProgramEntry() {
		final Set<ACTION> result = new HashSet<>();
		final String initialProcedure = mTopologicalOrder.get(0);
		result.addAll(
				mTransitionProvider.getSuccessorActions((LOC) mIcfg.getProcedureEntryNodes().get(initialProcedure)));
		return result;
	}

	public Set<ACTION> getSelfReachableReads(final String procedure) {
		return mSelfReachableReads.getImage(procedure);
	}

	public Set<ACTION> getPossibleWrites(final ACTION read) {
		return mWritesPerRead.get(read);
	}

	public Set<LOC> forkedAt(final String procedure) {
		return mForkedAt.getImage(procedure);
	}

	public Set<Map<LOC, Set<ACTION>>> getCrossProduct(final IFilter<ACTION, LOC> filter, final String procedure) {
		final var crossProduct = mCrossProducts.get(procedure);
		if (crossProduct == null) {
			return computeCrossProduct(filter, procedure);
		}
		return crossProduct;
	}

	public Set<ACTION> getWrites(final String procedure) {
		return mWritesPerProcedure.get(procedure);
	}

	public Set<ACTION> getReads(final String procedure) {
		return mReadsPerProcedure.get(procedure);

	}

	public Set<IProgramVarOrConst> getVarsForBuildingState(final ACTION action) {
		return DataStructureUtils.union(getWrittenVars(action), mSharedWriteReadVars.get(action));
	}

	public Set<IProgramVarOrConst> getWrittenVars(final ACTION action) {
		return mSharedWriteWrittenVars.getImage(action);
	}

	public Set<IProgramVarOrConst> getReadVars(final ACTION action) {
		return mSharedReadReadVars.getImage(action);
	}

	public boolean canReadFromInterference(final ACTION read, final ACTION write) {
		return mWritesPerRead.get(read).contains(write);
	}

	// Is function needed?
	public Map<ACTION, DisjunctiveAbstractState<STATE>> filterProcedures(final String name,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		final Map<ACTION, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		interferences.entrySet().stream().filter(a -> mTransitionProvider.getProcedureName(a.getKey()) != (name))
				.forEach(b -> result.put(b.getKey(), b.getValue()));
		return result;
	}

	public static <K, V> Map<K, V> copyMap(final Map<K, V> map) {
		final Map<K, V> result = new HashMap<>();
		map.forEach((a, b) -> result.put(a, b));
		return result;
	}

	public List<String> getTopologicalOrder() {
		return mTopologicalOrder;
	}

	private static Integer queueCompare(final Pair<String, Integer> pair1, final Pair<String, Integer> pair2) {
		// 1 < 2 => -1
		// 1 > 2 => 1
		// 1 == 2 => 0
		return pair1.getSecond() - pair2.getSecond();
	}

	/**
	 * pre computation over the icfg: shared write locations and share read locations
	 *
	 * @param entryNodes
	 */
	private void initialize(final Map<String, ? extends IcfgLocation> entryNodes) {
		final Set<IProgramVar> variables = new HashSet<>();
		entryNodes.forEach((procedure, location) -> variables
				.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure)));

		for (final var entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			iterator.asStream().forEach(edge -> computationsPerEdge(entry.getKey(), edge, variables));
		}
		// calculated until here: mReadSharedVars, mWrittenSharedVars, mWritesPerProcedure, mReadsPerProcedure

		final Map<ACTION, Set<String>> readsFromProcedures = new HashMap<>();

		for (final var entry : mReadsPerProcedure.entrySet()) {
			for (final ACTION action : entry.getValue()) {
				readsFromProcedures.put(action, new HashSet<>());
			}
		}

		for (final Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			for (final var edge : iterator.asStream().collect(Collectors.toSet())) {
				if (edge instanceof IForkActionThreadCurrent) {
					final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
					mForkedAt.addPair(fork.getNameOfForkedProcedure(), mTransitionProvider.getSource((ACTION) edge));
					addDependency(entry.getValue().getProcedure(), fork.getNameOfForkedProcedure());
					mForks.addPair(entry.getValue().getProcedure(), fork.getNameOfForkedProcedure());

					final IcfgEdgeIterator forkIterator = new IcfgEdgeIterator(edge.getTarget().getOutgoingEdges());
					forkIterator.asStream().forEach(
							a -> checkforInterferences(a, fork.getNameOfForkedProcedure(), readsFromProcedures));
				}
			}
		}

		final Map<String, Set<String>> closureDepending = closure(mDependingProcedures);
		final Map<String, Set<String>> dependingOn = computeDependingProcedures(closureDepending);

		for (final var entry : dependingOn.entrySet()) {
			if (entry.getValue().contains(entry.getKey())) {
				mParallelProcedures.add(entry.getKey());
			}
		}

		for (final Entry<ACTION, Set<String>> entry : readsFromProcedures.entrySet()) {
			mWritesPerRead.put(entry.getKey(), new HashSet<>());
			final Set<IProgramVarOrConst> readVars = getReadVars(entry.getKey());
			for (final String p1 : entry.getValue()) {

				// add all writes from procedure
				final Set<ACTION> writesP1 = mWritesPerProcedure.get(p1);
				if (writesP1 != null) {
					writesP1.stream()
							.filter(x -> DataStructureUtils.haveNonEmptyIntersection(getWrittenVars(x), readVars))
							.forEach(y -> mWritesPerRead.get(entry.getKey()).add(y));
				}
				// add all writes from closure(procedure)
				final Set<String> forkedByP1 = closureDepending.get(p1);
				if (forkedByP1 == null) {
					continue;
				}
				for (final String p2 : forkedByP1) {
					final Set<ACTION> writesP2 = mWritesPerProcedure.get(p2);
					if (writesP2 != null) {
						writesP2.stream()
								.filter(x -> DataStructureUtils.haveNonEmptyIntersection(getWrittenVars(x), readVars))
								.forEach(y -> mWritesPerRead.get(entry.getKey()).add(y));
					}
				}
			}
			// every Read in the procedure xy gets all procedure it depends on
			final Set<String> readDependsOn = dependingOn.get(mTransitionProvider.getProcedureName(entry.getKey()));
			if (readDependsOn == null) {
				continue;
			}
			for (final String p3 : readDependsOn) {
				final Set<ACTION> writesP3 = mWritesPerProcedure.get(p3);
				if (writesP3 != null) {
					writesP3.stream()
							.filter(x -> DataStructureUtils.haveNonEmptyIntersection(getWrittenVars(x), readVars))
							.forEach(y -> mWritesPerRead.get(entry.getKey()).add(y));
				}
			}
		}

		computeTopologicalOrder(entryNodes.keySet());
	}

	private static Map<String, Set<String>> closure(final Map<String, Set<String>> map) {
		// create deep copy of mForks
		final Map<String, Set<String>> result = new HashMap<>();
		for (final Entry<String, Set<String>> entry : map.entrySet()) {
			result.put(entry.getKey(), new HashSet<>());
			for (final String value : entry.getValue()) {
				result.get(entry.getKey()).add(value);
			}
		}
		boolean changes = true;
		while (changes) {
			changes = false;
			for (final Entry<String, Set<String>> entry : result.entrySet()) {
				final Set<String> tempSet = new HashSet<>();
				for (final String forked : entry.getValue()) {
					if (result.containsKey(forked) && !DataStructureUtils
							.difference(result.get(forked), result.get(entry.getKey())).isEmpty()) {
						tempSet.addAll(result.get(forked));
						changes = true;
					}
				}
				result.get(entry.getKey()).addAll(tempSet);
			}
		}
		return result;
	}

	private Map<String, Set<String>> computeDependingProcedures(final Map<String, Set<String>> closureForks) {
		final Map<String, Set<String>> result = new HashMap<>();
		final Queue<String> worklist = new ArrayDeque<>();
		final Set<String> added = new HashSet<>();
		final String startitem = "ULTIMATE.start";
		worklist.add(startitem);
		added.add(startitem);
		// initialize for every procedure the empty set
		mIcfg.getCfgSmtToolkit().getProcedures().forEach(p -> result.put(p, new HashSet<>()));
		while (!worklist.isEmpty()) {
			final String currentItem = worklist.poll();
			if (!mDependingProcedures.containsKey(currentItem)) {
				continue;
			}
			for (final String forked : mDependingProcedures.get(currentItem)) {
				// copy all entries von item into child
				result.get(forked).addAll(result.get(currentItem));
				// add parent
				result.get(forked).add(currentItem);
				// add all other children
				final Set<String> otherChildren = mDependingProcedures.get(currentItem).stream()
						.filter(a -> !a.equals(forked)).collect(Collectors.toSet());
				result.get(forked).addAll(otherChildren);
				// add closure over all other children
				for (final String child : otherChildren) {
					if (closureForks.containsKey(child)) {
						result.get(forked).addAll(closureForks.get(child));
					}
				}

				if (!added.contains(forked)) {
					worklist.add(forked);
					added.add(forked);
				}
			}
		}
		return result;
	}

	private void checkforInterferences(final IcfgEdge edge, final String currentProcedure,
			final Map<ACTION, Set<String>> map) {
		// check if edge is sharedRead
		if (mSharedReadReadVars.getDomain().contains(edge)) {
			map.get(edge).add(currentProcedure);
		}

		if (edge instanceof IForkActionThreadCurrent
				&& ((IForkActionThreadCurrent) edge).getNameOfForkedProcedure().equals(currentProcedure)) {
			// Procedures running parallel -> co-dependent
			final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
			addDependency(currentProcedure, fork.getNameOfForkedProcedure());
		}
	}

	private void addDependency(final String forks, final String forkedProcedure) {
		final Set<String> tempSet;
		if (mDependingProcedures.containsKey(forks)) {
			tempSet = mDependingProcedures.get(forks);
		} else {
			tempSet = new HashSet<>();
		}
		tempSet.add(forkedProcedure);
		mDependingProcedures.put(forks, tempSet);
	}

	private void computationsPerEdge(final String procedure, final IcfgEdge edge, final Set<IProgramVar> variables) {
		mActionsInProcedure.addPair(procedure, (ACTION) edge);
		// SharedWrites
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getAssignedVars(), variables)) {
			mSharedWriteReadVars.put((ACTION) edge, new HashSet<>());
			mSharedWriteReadVars.get(edge).addAll(edge.getTransformula().getInVars().keySet());

			edge.getTransformula().getAssignedVars().stream()
					.forEach(var -> mSharedWriteWrittenVars.addPair((ACTION) edge, var));
			if (mWritesPerProcedure.containsKey(procedure)) {
				mWritesPerProcedure.get(procedure).add((ACTION) edge);
			} else {
				final Set<ACTION> tempSet = new HashSet<>();
				tempSet.add((ACTION) edge);
				mWritesPerProcedure.put(procedure, tempSet);
			}
		}
		// SharedReads
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getInVars().keySet(), variables)) {
			DataStructureUtils.intersection(edge.getTransformula().getInVars().keySet(), variables)
					.forEach(var -> mSharedReadReadVars.addPair((ACTION) edge, var));
			if (mReadsPerProcedure.containsKey(procedure)) {
				mReadsPerProcedure.get(procedure).add((ACTION) edge);
			} else {
				final Set<ACTION> tempSet = new HashSet<>();
				tempSet.add((ACTION) edge);
				mReadsPerProcedure.put(procedure, tempSet);
			}

			if (isSelfReachable(edge)) {
				mSelfReachableReads.addPair(procedure, (ACTION) edge);
			}

		}
	}

	private static boolean isSelfReachable(final IcfgEdge action) {
		final IcfgEdgeIterator edgeIterator = new IcfgEdgeIterator(action.getTarget().getOutgoingEdges());
		return edgeIterator.asStream().anyMatch(edge -> edge.equals(action));
	}

	private Set<Map<LOC, Set<ACTION>>> computeCrossProduct(final IFilter<ACTION, LOC> filter, final String procedure) {
		final Set<Map<LOC, Set<ACTION>>> result = new HashSet<>();
		// LinkedHashMap, because Iteration order must stay the same
		// reads can read from several global variables -> should LOC - Set<ACTION>
		final Map<LOC, List<Set<ACTION>>> writes = new LinkedHashMap<>();
		int n = 1;
		final Set<ACTION> dummy = null;
		final Set<ACTION> reads = getReads(procedure);
		final Set<ACTION> selfReachable = getSelfReachableReads(procedure);
		if (reads != null) {
			for (final var read : reads) {
				if (selfReachable.contains(read)) {
					// reads in loops are handled separately
					continue;
				}

				final LOC source = mTransitionProvider.getSource(read);
				if (writes.containsKey(source)) {
					continue;
				}

				final List<Set<ACTION>> tempList =
						computeCrossProductOfWrites(sortWritesAfterVariables(mWritesPerRead.get(read)), read);
				if (tempList.isEmpty()) {
					continue;
				}
				n *= tempList.size();
				writes.put(source, tempList);
			}

			for (int i = 0; i < n; i++) {
				int blocksize = 1;
				final Map<LOC, Set<ACTION>> map = new HashMap<>();
				for (final var readEntry : writes.entrySet()) {
					final int index = (i / blocksize) % readEntry.getValue().size();
					final Set<ACTION> write = readEntry.getValue().get(index);
					// if (write != null) {
					// TODO: if computeDummyWrites is implemented delete if-condition
					map.put(readEntry.getKey(), write);
					// }
					blocksize *= readEntry.getValue().size();
				}
				if (!map.isEmpty() && filter.evaluate(map)) {
					result.add(map);
				}
			}
		}

		mCrossProducts.put(procedure, result);
		return result;
	}

	private List<Set<ACTION>> computeCrossProductOfWrites(
			final HashRelation<IProgramVarOrConst, ACTION> writesPerVariable, final ACTION read) {
		List<Set<ACTION>> result = new ArrayList<>();

		final Set<ACTION> entryActions = getFirstActions();
		for (final IProgramVarOrConst variable : writesPerVariable.getDomain()) {
			if (canBeUninitialized(variable, read, entryActions)) {
				writesPerVariable.addPair(variable, null);
			}
		}

		for (final var entry : writesPerVariable.entrySet()) {
			final List<Set<ACTION>> newResult = new ArrayList<>();
			for (final ACTION action : entry.getValue()) {
				if (result.isEmpty()) {
					final Set<ACTION> actionSet = new HashSet<>();
					actionSet.add(action);
					newResult.add(actionSet);
					continue;
				}

				for (final Set<ACTION> set : result) {
					final Set<ACTION> tempSet = set.stream().collect(Collectors.toSet());
					tempSet.add(action);
					newResult.add(tempSet);
				}
			}
			result = newResult;
		}

		return result;
	}

	private HashRelation<IProgramVarOrConst, ACTION> sortWritesAfterVariables(final Set<ACTION> writes) {
		final HashRelation<IProgramVarOrConst, ACTION> writesPerVariable = new HashRelation<>();
		if (writes.isEmpty()) {
			return writesPerVariable;
		}
		for (final var action : writes) {
			getWrittenVars(action).forEach(variable -> writesPerVariable.addPair(variable, action));
		}
		return writesPerVariable;
	}

	private boolean canBeUninitialized(final IProgramVarOrConst variable, final ACTION read,
			final Set<ACTION> entryActions) {
		final Queue<ACTION> workList = new ArrayDeque<>();
		workList.add(read);
		final Set<ACTION> done = new HashSet<>();
		final Set<ACTION> allWritesToVariable = mSharedWriteWrittenVars.getDomain().stream()
				.filter(write -> mSharedWriteWrittenVars.getImage(write).contains(variable))
				.collect(Collectors.toSet());
		while (!workList.isEmpty()) {
			final ACTION currentItem = workList.poll();
			if (allWritesToVariable.contains(currentItem)) {
				continue;
			}
			if (entryActions.contains(currentItem)) {
				return true;
			}
			final LOC source = mTransitionProvider.getSource(currentItem);
			final Collection<ACTION> predecessors = mTransitionProvider.getPredecessorActions(source);
			if (predecessors.isEmpty()) {
				// source is ThreadEntry
				for (final var fork : mForkedAt.getImage(mTransitionProvider.getProcedureName(currentItem))) {
					workList.addAll(mTransitionProvider.getPredecessorActions(fork));
				}
				continue;
			}
			for (final var predecessor : predecessors) {
				if (!done.contains(predecessor)) {
					workList.add(predecessor);
				}
			}
			done.add(currentItem);
		}
		return false;
	}

	private Set<ACTION> getFirstActions() {
		final IcfgLocation start = mIcfg.getProcedureEntryNodes().get(mTopologicalOrder.get(0));
		return new HashSet<>(mTransitionProvider.getSuccessorActions((LOC) start));
	}

	private void computeTopologicalOrder(final Set<String> procedures) {
		final Map<String, Integer> inGrad = new HashMap<>();
		for (final String procedure : procedures) {
			inGrad.put(procedure, 0);
		}

		for (final var entry : mForks.entrySet()) {
			for (final String forked : entry.getValue()) {
				inGrad.put(forked, inGrad.get(forked) + 1);
			}
		}

		final PriorityQueue<Pair<String, Integer>> pQueue = new PriorityQueue<>((x, y) -> queueCompare(x, y));

		for (final var entry : inGrad.entrySet()) {
			pQueue.add(new Pair<>(entry.getKey(), entry.getValue()));
		}

		final Set<String> visited = new HashSet<>();

		while (!DataStructureUtils.difference(procedures, visited).isEmpty()) {
			final Pair<String, Integer> currentItem = pQueue.poll();
			if (currentItem.getSecond() == 0) {
				final String key = currentItem.getFirst();
				if (!visited.contains(key)) {
					mTopologicalOrder.add(key);
					visited.add(key);

					for (final String forked : mForks.getImage(key)) {
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
				mTopologicalOrder.add(procedure);
			}
			break;
		}
	}
}
