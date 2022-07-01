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
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
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

/**
 *
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 *
 */

public class FixpointEngineConcurrentUtils<STATE extends IAbstractState<STATE>, ACTION, LOC> {

	private final IIcfg<?> mIcfg;
	private final ITransitionProvider<ACTION, LOC> mTransitionProvider;
	private final Map<ACTION, Set<IProgramVarOrConst>> mWrittenSharedVars;
	private final Map<ACTION, Set<IProgramVarOrConst>> mReadSharedVars;
	private final Map<String, Set<String>> mForks;
	private final Map<ACTION, Set<String>> mReadsFromProcedures;
	private final Map<String, Set<ACTION>> mWritesPerProcedure;
	private final Map<String, Set<ACTION>> mReadsPerProcedure;

	public FixpointEngineConcurrentUtils(final IIcfg<?> icfg, final ITransitionProvider<ACTION, LOC> transProvider) {
		mIcfg = icfg;
		mTransitionProvider = transProvider;
		mWrittenSharedVars = new HashMap<>();
		mReadSharedVars = new HashMap<>();
		mForks = new HashMap<>();
		mReadsFromProcedures = new HashMap<>();
		mWritesPerProcedure = new HashMap<>();
		mReadsPerProcedure = new HashMap<>();

		initialize(mIcfg.getProcedureEntryNodes());
	}

	public Set<ACTION> getWrites(final String procedure) {
		return mWritesPerProcedure.get(procedure);
	}

	public Set<ACTION> getReads(final String procedure) {
		return mReadsPerProcedure.get(procedure);
	}

	public Set<IProgramVarOrConst> getWrittenVars(final ACTION action) {
		return mWrittenSharedVars.get(action);
	}

	public Set<IProgramVarOrConst> getReadVars(final ACTION action) {
		return mReadSharedVars.get(action);
	}

	public Set<Entry<ACTION, Set<IProgramVarOrConst>>> getSharedWriteIterable() {
		return mWrittenSharedVars.entrySet();
	}

	public Set<Entry<ACTION, Set<IProgramVarOrConst>>> getSharedReadIterable() {
		return mReadSharedVars.entrySet();
	}

	public boolean canReadFromInterference(final ACTION read, final String writeProcedure) {
		return mReadsFromProcedures.get(read).contains(writeProcedure);
	}

	public Map<ACTION, DisjunctiveAbstractState<STATE>> filterProcedures(final String name,
			final Map<ACTION, DisjunctiveAbstractState<STATE>> interferences) {
		// TODO: check nicer way via .collect ???
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

		for (final var entry : mReadSharedVars.entrySet()) {
			mReadsFromProcedures.put(entry.getKey(), new HashSet<>());
		}

		for (final Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			for (final var edge : iterator.asStream().collect(Collectors.toSet())) {
				if (edge instanceof IForkActionThreadCurrent) {
					final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
					addFork(entry.getValue().getProcedure(), fork.getNameOfForkedProcedure());

					final IcfgEdgeIterator forkIterator = new IcfgEdgeIterator(edge.getTarget().getOutgoingEdges());
					forkIterator.asStream().forEach(a -> checkforInterferences(a, fork.getNameOfForkedProcedure()));
				}
			}
		}

		final Map<String, Set<String>> closureForks = closure(mForks);
		final Map<String, Set<String>> dependingOn = computeDependingProcedures(closureForks);

		for (final Entry<ACTION, Set<String>> entry : mReadsFromProcedures.entrySet()) {
			// every Read that has xy in mReadsFromProcedures gets all mForks.get(xy) added
			final Set<String> tempSet = new HashSet<>();
			for (final String procedure : entry.getValue()) {
				if (closureForks.containsKey(procedure)) {
					tempSet.addAll(closureForks.get(procedure));
				}
			}
			mReadsFromProcedures.get(entry.getKey()).addAll(tempSet);

			// every Read in the procedure xy gets all mParallelProcedures.get(xy) added
			if (dependingOn.containsKey(mTransitionProvider.getProcedureName(entry.getKey()))) {
				mReadsFromProcedures.get(entry.getKey())
						.addAll(dependingOn.get(mTransitionProvider.getProcedureName(entry.getKey())));
			}
		}

		final boolean timestop = true;
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
		// TODO: Compute mDependingOn Map<String, String>
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
			if (!mForks.containsKey(currentItem)) {
				continue;
			}
			for (final String forked : mForks.get(currentItem)) {
				// copy all entries von item into child
				result.get(forked).addAll(result.get(currentItem));
				// add parent
				result.get(forked).add(currentItem);
				// add all other children
				final Set<String> otherChildren =
						mForks.get(currentItem).stream().filter(a -> !a.equals(forked)).collect(Collectors.toSet());
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

	private void checkforInterferences(final IcfgEdge edge, final String currentProcedure) {
		if (mReadSharedVars.containsKey(edge)) {
			mReadsFromProcedures.get(edge).add(currentProcedure);
		}

		if (edge instanceof IForkActionThreadCurrent
				&& ((IForkActionThreadCurrent) edge).getNameOfForkedProcedure().equals(currentProcedure)) {
			// Procedures running parallel -> co-dependent
			final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
			addFork(currentProcedure, fork.getNameOfForkedProcedure());
		}
	}

	private void addFork(final String forks, final String forkedProcedure) {
		final Set<String> tempSet;
		if (mForks.containsKey(forks)) {
			tempSet = mForks.get(forks);
		} else {
			tempSet = new HashSet<>();
		}
		tempSet.add(forkedProcedure);
		mForks.put(forks, tempSet);
	}

	private void computationsPerEdge(final String procedure, final IcfgEdge edge, final Set<IProgramVar> variables) {
		// SharedWrites
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getAssignedVars(), variables)) {
			mReadSharedVars.put((ACTION) edge, new HashSet<>());
			edge.getTransformula().getInVars().keySet().forEach(var -> mReadSharedVars.get(edge).add(var));

			mWrittenSharedVars.put((ACTION) edge, new HashSet<>());
			edge.getTransformula().getAssignedVars().forEach(var -> mWrittenSharedVars.get(edge).add(var));
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
			mReadSharedVars.put((ACTION) edge, new HashSet<>());
			DataStructureUtils.intersection(edge.getTransformula().getInVars().keySet(), variables)
					.forEach(var -> mReadSharedVars.get(edge).add(var));
			if (mReadsPerProcedure.containsKey(procedure)) {
				mReadsPerProcedure.get(procedure).add((ACTION) edge);
			} else {
				final Set<ACTION> tempSet = new HashSet<>();
				tempSet.add((ACTION) edge);
				mReadsPerProcedure.put(procedure, tempSet);
			}
		}
	}
}
