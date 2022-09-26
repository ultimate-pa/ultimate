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
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.PriorityQueue;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IForkActionThreadCurrent;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;
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
	private final ILogger mLogger;
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
	private final HashRelation<ACTION, ACTION> mDominates;

	private final Set<IProgramVarOrConst> mGlobalVars;

	private final Collection<Set<IProgramVarOrConst>> mDependenciesBetweenVars;

	private final Map<String, Set<Map<LOC, Set<ACTION>>>> mCrossProducts;

	public FixpointEngineConcurrentUtils(final IIcfg<?> icfg, final ITransitionProvider<ACTION, LOC> transProvider,
			final ILogger logger) {
		mIcfg = icfg;
		mTransitionProvider = transProvider;
		mLogger = logger;
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
		mDependenciesBetweenVars = new HashSet<>();
		mDominates = new HashRelation<>();
		mGlobalVars = new HashSet<>();

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
		result.add(getDominates());
		result.add(getNotReachableFrom(entryNodes));
		result.add(getThCreates(entryNodes));
		result.add(getThJoins());
		return result;
	}

	/***
	 *
	 * @param entryNodes
	 * @return MHB: (x,y) in MHB, iff (x,y) in DOMINATES and (x,y) in NOTREACHABLEFROM
	 */
	public HashRelation<ACTION, ACTION> getMustHappenBefore(final Map<String, ? extends IcfgLocation> entryNodes) {
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		final HashRelation<ACTION, ACTION> notRechableFrom = getNotReachableFrom(entryNodes);
		for (final var entry : mDominates.getSetOfPairs()) {
			if (notRechableFrom.getImage(entry.getKey()).contains(entry.getValue())) {
				result.addPair(entry.getKey(), entry.getValue());
			}
		}

		return result;
	}

	/***
	 *
	 * @return DOMINATES: (x,y) in DOMINATES, iff all paths from the thread entry to y contain x.
	 */
	public HashRelation<ACTION, ACTION> getDominates() {
		return mDominates;
	}

	/***
	 *
	 * @return NOTREACHABLEFROM: (x,y) in NOTREACHABLEFROM, iff x is not reachable from y.
	 */
	public HashRelation<ACTION, ACTION> getNotReachableFrom(final Map<String, ? extends IcfgLocation> entryNodes) {
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();

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

	/***
	 *
	 * @return All actions that are a successor of entry locations from procedures which can run parallel to itself.
	 */
	public Set<ACTION> getParallelProcedureEntrys() {
		final Set<ACTION> result = new HashSet<>();
		for (final var entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			if (mParallelProcedures.contains(entry.getKey())) {
				result.addAll(mTransitionProvider.getSuccessorActions((LOC) entry.getValue()));
			}
		}
		return result;
	}

	/***
	 *
	 * @return All actions that are a successor of entry locations from procedures which can <b>not </b> run parallel to
	 *         itself.
	 */
	public Set<ACTION> getNormalProcedureEntrys() {
		final Set<ACTION> result = new HashSet<>();
		for (final var entry : mIcfg.getProcedureEntryNodes().entrySet()) {
			if (!mParallelProcedures.contains(entry.getKey())) {
				result.addAll(mTransitionProvider.getSuccessorActions((LOC) entry.getValue()));
			}
		}
		return result;
	}

	/***
	 *
	 * @return All actions that are a successor of the entry location of the whole program.
	 */
	public Set<ACTION> getProgramEntries() {
		final IcfgLocation start = mIcfg.getProcedureEntryNodes().get(mTopologicalOrder.get(0));
		return new HashSet<>(mTransitionProvider.getSuccessorActions((LOC) start));
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

	/***
	 * If the cross-product for the procedure is not computed yet, it will be computed intern (may take some time). The
	 * cross-product contains initially every combination of read-write-combinations and will then be filtered.
	 *
	 * @param filter
	 * @param procedure
	 * @return
	 */
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

	/***
	 *
	 * @param action
	 * @return All variables that will either be written or read in that statement
	 */
	public Set<IProgramVarOrConst> getVarsForBuildingState(final ACTION action) {
		return DataStructureUtils.union(getWrittenVars(action), mSharedWriteReadVars.get(action));
	}

	public Set<IProgramVarOrConst> getWrittenVars(final ACTION action) {
		return mSharedWriteWrittenVars.getImage(action);
	}

	public Set<IProgramVarOrConst> getReadVars(final ACTION action) {
		return mSharedReadReadVars.getImage(action);
	}

	public Set<IProgramVarOrConst> getGlobalVars() {
		return mGlobalVars;
	}

	public boolean canReadFromInterference(final ACTION read, final ACTION write) {
		return mWritesPerRead.get(read).contains(write);
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
		return pair1.getSecond() - pair2.getSecond();
	}

	private void initialize(final Map<String, ? extends IcfgLocation> entryNodes) {

		final Set<IProgramVar> variables = new HashSet<>();
		entryNodes.forEach((procedure, location) -> variables
				.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure)));

		for (final var entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			iterator.asStream().forEach(edge -> computationsPerEdge(entry.getKey(), edge, variables));
		}

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

		computeTopologicalOrder(entryNodes.keySet());
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

		computeGlobalVars();
		computeDependenciesBetweenVars();
	}

	/***
	 * Compute transitive closure over relation
	 *
	 * @param map
	 * @return
	 */
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
		final String startitem = getTopologicalOrder().get(0);
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
		Set<Map<LOC, Set<ACTION>>> result = new HashSet<>();
		for (final var variables : mDependenciesBetweenVars) {
			final Set<Map<LOC, Set<ACTION>>> temp = computeCrossProductForSetOfVars(filter, procedure, variables);
			if (result.isEmpty()) {
				result.addAll(temp);
				continue;
			}
			result = mergeCombinations(result, temp);
		}

		mCrossProducts.put(procedure, result);
		return result;
	}

	private Set<Map<LOC, Set<ACTION>>> computeCrossProductForSetOfVars(final IFilter<ACTION, LOC> filter,
			final String procedure, final Set<IProgramVarOrConst> variables) {
		mLogger.info("Cross Product Computation started for " + procedure + " with variables: " + variables);
		final Set<Map<LOC, Set<ACTION>>> result = new HashSet<>();
		// LinkedHashMap, because Iteration order must stay the same
		final Map<LOC, List<Set<ACTION>>> writes = new LinkedHashMap<>();
		int n = 1;
		final Set<ACTION> reads = getReads(procedure);
		final Set<ACTION> selfReachable = getSelfReachableReads(procedure);
		if (reads != null) {
			for (final var read : reads) {
				if (selfReachable.contains(read)) {
					// reads in loops are handled separately
					continue;
				}

				if (DataStructureUtils.haveEmptyIntersection(getReadVars(read), variables)) {
					// read is independent from variables
					continue;
				}

				final LOC source = mTransitionProvider.getSource(read);
				if (writes.containsKey(source)) {
					// read is an assume and counterpart of the assume has the same writes
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

			mLogger.info("Start checking " + n + " possible combinations.");
			for (int i = 0; i < n; i++) {
				int blocksize = 1;
				final Map<LOC, Set<ACTION>> map = new HashMap<>();
				for (final var readEntry : writes.entrySet()) {
					final int index = (i / blocksize) % readEntry.getValue().size();
					final Set<ACTION> write = readEntry.getValue().get(index);
					map.put(readEntry.getKey(), write);
					blocksize *= readEntry.getValue().size();
				}

				mLogger.info("Filter Iteration " + (i + 1) + "/" + n);
				if (!map.isEmpty() && filter.evaluate(map)) {
					result.add(map);
				} else {
					mLogger.info("contradiction");
				}
			}
		}

		mLogger.info("Number of combinations: " + result.size());
		return result;
	}

	private List<Set<ACTION>> computeCrossProductOfWrites(
			final HashRelation<IProgramVarOrConst, ACTION> writesPerVariable, final ACTION read) {
		List<Set<ACTION>> result = new ArrayList<>();

		final Set<ACTION> entryActions = getProgramEntries();
		for (final IProgramVarOrConst variable : writesPerVariable.getDomain()) {
			writesPerVariable.addAllPairs(variable, checkDummyWrite(variable, read, entryActions));
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

	/***
	 * Find last writes which the read can from, iff the program is executed sequential.
	 *
	 * @param variable
	 * @param read
	 * @param entryActions
	 * @return
	 */
	private Set<ACTION> checkDummyWrite(final IProgramVarOrConst variable, final ACTION read,
			final Set<ACTION> entryActions) {
		final Set<ACTION> result = new HashSet<>();
		final Queue<ACTION> workList = new ArrayDeque<>();
		workList.add(read);
		final Set<ACTION> done = new HashSet<>();
		final Set<ACTION> allWritesToVariable = mSharedWriteWrittenVars.getDomain().stream()
				.filter(write -> mSharedWriteWrittenVars.getImage(write).contains(variable))
				.collect(Collectors.toSet());
		// BFS backwards through CFG starting at read
		while (!workList.isEmpty()) {
			final ACTION currentItem = workList.poll();
			if (allWritesToVariable.contains(currentItem)) {
				if (mTransitionProvider.getProcedureName(read) == mTransitionProvider.getProcedureName(currentItem)) {
					result.add(currentItem);
				}
				continue;
			}
			if (entryActions.contains(currentItem)) {
				result.add(null);
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
		return result;
	}

	private Set<Map<LOC, Set<ACTION>>> mergeCombinations(final Set<Map<LOC, Set<ACTION>>> comb1,
			final Set<Map<LOC, Set<ACTION>>> comb2) {
		final Set<Map<LOC, Set<ACTION>>> result = new HashSet<>();
		Iterator<Map<LOC, Set<ACTION>>> bigger;
		Iterator<Map<LOC, Set<ACTION>>> smaller;

		if (comb1.size() >= comb2.size()) {
			bigger = comb1.iterator();
			smaller = comb2.iterator();
		} else {
			bigger = comb2.iterator();
			smaller = comb1.iterator();
		}

		while (smaller.hasNext()) {
			final Map<LOC, Set<ACTION>> map1 = smaller.next();
			final Map<LOC, Set<ACTION>> map2 = bigger.next();
			// keys in map1 and map2 are independent, because they resulted from disjunct sets of variables
			map1.putAll(map2);
			result.add(map1);
		}
		bigger.forEachRemaining(map -> result.add(map));
		return result;
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

	/***
	 * Two variables are dependent if they are data-dependent or control-dependent. They are data-dependent if the value
	 * of y (directly) influences the computation of x. They are control-dependent if x is part of a statement and it
	 * depends on y, whether the statement will be executed or not.
	 */
	private void computeDependenciesBetweenVars() {
		final UnionFind<IProgramVarOrConst> result = new UnionFind<>();
		final Set<IProgramVarOrConst> nonGlobalVars = new HashSet<>();

		// compute data-dependency between writes
		for (final var procedure : mTopologicalOrder) {
			for (final var variable : mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable()
					.getModifiedBoogieVars(procedure)) {
				if (result.find(variable) == null) {
					result.makeEquivalenceClass(variable);
				}
			}

			// Iterate over CFG
			final IcfgEdgeIterator iterator =
					new IcfgEdgeIterator(mIcfg.getProcedureEntryNodes().get(procedure).getOutgoingEdges());
			while (iterator.hasNext()) {
				final IcfgEdge edge = iterator.next();
				if (isWrite(edge)) {
					final Set<IProgramVarOrConst> variables = new HashSet<>();
					DataStructureUtils.union(edge.getTransformula().getAssignedVars(),
							edge.getTransformula().getInVars().keySet()).forEach(x -> variables.add(x));
					for (final var variable : variables) {
						if (result.find(variable) == null) {
							nonGlobalVars.add(variable);
							result.makeEquivalenceClass(variable);
						}
					}
					result.union(variables);
				}
			}
		}

		if (result.size() == 1) {
			result.removeAll(nonGlobalVars);
			mDependenciesBetweenVars.addAll(result.getAllEquivalenceClasses());
			return;
		}

		// control dependency
		final HashRelation<ACTION, ACTION> controlDependent = computeControlDependency();

		for (final var entry : controlDependent.entrySet()) {
			final Set<IProgramVarOrConst> variables = new HashSet<>();
			boolean flag = false;
			if (isWrite((IcfgEdge) entry.getKey())) {
				flag = true;
				variables.addAll(getAllVars(entry.getKey()));
			}
			if (entry.getKey() instanceof IForkActionThreadCurrent) {
				flag = true;
				final String procedure = mTransitionProvider.getProcedureName(entry.getKey());
				variables.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure));
			}

			if (flag) {
				for (final var value : entry.getValue()) {
					if (value instanceof IcfgEdge) {
						variables.addAll(((IcfgEdge) value).getTransformula().getInVars().keySet());
					}
				}
				result.union(variables);
			}
		}

		result.removeAll(nonGlobalVars);
		mDependenciesBetweenVars.addAll(result.getAllEquivalenceClasses());
	}

	private Set<IProgramVarOrConst> getAllVars(final ACTION action) {
		if (action instanceof IcfgEdge) {
			final Set<IProgramVarOrConst> result = new HashSet<>();
			final IcfgEdge edge = (IcfgEdge) action;
			result.addAll(edge.getTransformula().getAssignedVars());
			result.addAll(edge.getTransformula().getInVars().keySet());
			return result;
		}
		return null;

	}

	private static boolean isWrite(final IcfgEdge edge) {
		return !edge.getTransformula().getAssignedVars().isEmpty();
	}

	private HashRelation<ACTION, ACTION> computePostDominatedBy() {
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		final Set<LOC> loopHeads = (Set<LOC>) mIcfg.getLoopLocations();

		for (final var procedure : mTopologicalOrder) {
			final Queue<LOC> workList = new ArrayDeque<>();
			final Set<LOC> done = new HashSet<>();

			final LOC exit = (LOC) mIcfg.getProcedureExitNodes().get(procedure);
			// initialize to exit node
			for (final var action : mTransitionProvider.getPredecessorActions(exit)) {
				result.addPair(action, action);
				workList.add(mTransitionProvider.getSource(action));
				done.add(mTransitionProvider.getTarget(action));
			}

			// add ErrorLocations
			final var errors = mIcfg.getProcedureErrorNodes().get(procedure);
			if (errors != null) {
				for (final var error : errors) {
					for (final var action : mTransitionProvider.getPredecessorActions((LOC) error)) {
						result.addPair(action, action);
						done.add(mTransitionProvider.getTarget(action));
					}
				}
			}

			while (!workList.isEmpty()) {
				final LOC item = workList.poll();

				if (!nodeReady(mTransitionProvider.getSuccessorActions(item), result) && !loopHeads.contains(item)) {
					continue;
				}

				Set<ACTION> intersection = new HashSet<>();
				for (final var action : mTransitionProvider.getSuccessorActions(item)) {
					final Set<ACTION> temp = result.getImage(action);
					if (temp.isEmpty()) {
						continue;
					}
					if (intersection.isEmpty()) {
						intersection = temp;
						continue;
					}
					intersection = DataStructureUtils.intersection(intersection, temp);
				}

				for (final var action : mTransitionProvider.getPredecessorActions(item)) {
					result.addPair(action, action);
					result.addAllPairs(action, intersection);
					final LOC source = mTransitionProvider.getSource(action);
					if (!done.contains(source)) {
						workList.add(source);
					}
				}

				done.add(item);
			}
		}
		return result;
	}

	private HashRelation<ACTION, ACTION> computeDominates() {
		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		final HashRelation<ACTION, ACTION> dominatedBy = new HashRelation<>();
		final Set<LOC> loopHeads = (Set<LOC>) mIcfg.getLoopLocations();

		for (final var procedure : mTopologicalOrder) {
			final Queue<LOC> workList = new ArrayDeque<>();
			final Set<LOC> done = new HashSet<>();

			final LOC entry = (LOC) mIcfg.getProcedureEntryNodes().get(procedure);
			// initialize to entry node
			for (final var action : mTransitionProvider.getSuccessorActions(entry)) {
				dominatedBy.addPair(action, action);
				result.addPair(action, action);
				workList.add(mTransitionProvider.getTarget(action));
				done.add(mTransitionProvider.getSource(action));
			}

			while (!workList.isEmpty()) {
				final LOC item = workList.poll();

				if (!nodeReady(mTransitionProvider.getPredecessorActions(item), dominatedBy)
						&& !loopHeads.contains(item)) {
					continue;
				}

				Set<ACTION> intersection = new HashSet<>();
				for (final var action : mTransitionProvider.getPredecessorActions(item)) {
					final Set<ACTION> temp = dominatedBy.getImage(action);
					if (temp.isEmpty()) {
						continue;
					}
					if (intersection.isEmpty()) {
						intersection = temp;
						continue;
					}
					intersection = DataStructureUtils.intersection(intersection, temp);
				}

				for (final var action : mTransitionProvider.getSuccessorActions(item)) {
					dominatedBy.addPair(action, action);
					dominatedBy.addAllPairs(action, intersection);
					result.addPair(action, action);
					intersection.forEach(x -> result.addPair(x, action));
					final LOC target = mTransitionProvider.getTarget(action);
					if (!done.contains(target)) {
						workList.add(target);
					}
				}

				done.add(item);
			}
		}

		for (final var entry : result.entrySet()) {
			mDominates.addAllPairs(entry.getKey(), entry.getValue());
		}
		return result;
	}

	/***
	 * a is control dependent on b iff the execution of a is dependent on b.
	 *
	 * @param dominates
	 * @return
	 */
	private HashRelation<ACTION, ACTION> computeControlDependency() {
		final HashRelation<ACTION, ACTION> dominates = computeDominates();
		final HashRelation<ACTION, ACTION> postDominated = computePostDominatedBy();

		final HashRelation<ACTION, ACTION> result = new HashRelation<>();
		for (final var entry : dominates.entrySet()) {
			if (!isSplitting(entry.getKey())) {
				continue;
			}
			entry.getValue().stream().filter(x -> isControlDependent(entry.getKey(), x, postDominated))
					.forEach(y -> result.addPair(y, entry.getKey()));
		}

		return result;
	}

	private boolean isControlDependent(final ACTION assume, final ACTION action,
			final HashRelation<ACTION, ACTION> postDominated) {
		final Iterator<ACTION> iterator =
				mTransitionProvider.getSuccessorActions(mTransitionProvider.getSource(assume)).iterator();
		Set<ACTION> intersection = postDominated.getImage(iterator.next());
		while (iterator.hasNext()) {
			intersection = DataStructureUtils.intersection(intersection, postDominated.getImage(iterator.next()));
		}

		return !action.equals(assume) && !intersection.contains(action);
	}

	private boolean isSplitting(final ACTION start) {
		final LOC temp = mTransitionProvider.getSource(start);
		return mTransitionProvider.getSuccessorActions(temp).size() > 1;
	}

	private boolean nodeReady(final Collection<ACTION> actions, final HashRelation<ACTION, ACTION> relation) {
		for (final var action : actions) {
			if (relation.getImage(action).isEmpty()) {
				return false;
			}
		}

		return true;
	}

	private void computeGlobalVars() {
		for (final var procedure : mTopologicalOrder) {
			mGlobalVars.addAll(mIcfg.getCfgSmtToolkit().getModifiableGlobalsTable().getModifiedBoogieVars(procedure));
		}
	}
}
