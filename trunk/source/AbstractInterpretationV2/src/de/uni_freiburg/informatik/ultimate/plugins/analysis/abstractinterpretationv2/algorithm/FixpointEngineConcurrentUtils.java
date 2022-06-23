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

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;
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
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 *
 * @author Johannes Wahl (johannes.wahl@merkur.uni-freiburg.de)
 *
 */

public class FixpointEngineConcurrentUtils<STATE extends IAbstractState<STATE>, ACTION, LOC> {

	private final IIcfg<?> mIcfg;
	private final Map<LOC, Set<IProgramVar>> mWrittenSharedVars;
	private final Map<ACTION, Set<IProgramVar>> mReadSharedVars;
	private final Map<LOC, String> mLoc2Procedure;
	private final Map<ACTION, String> mAction2Procedure;
	private final Map<LOC, ACTION> mLoc2Action;
	private final Map<String, Set<String>> mForks;
	private final Map<String, Set<String>> mParallelProcedures;
	private final Map<ACTION, Set<ACTION>> mActionsToPatch;
	private final Map<ACTION, Set<String>> mReadProcedures;

	public FixpointEngineConcurrentUtils(final IIcfg<?> icfg) {
		mIcfg = icfg;
		mWrittenSharedVars = new HashMap<>();
		mReadSharedVars = new HashMap<>();
		mLoc2Procedure = new HashMap<>();
		mLoc2Action = new HashMap<>();
		mAction2Procedure = new HashMap<>();
		mActionsToPatch = new HashMap<>();
		mForks = new HashMap<>();
		mParallelProcedures = new HashMap<>();
		mReadProcedures = new HashMap<>();

		initialize(mIcfg.getProcedureEntryNodes());
	}

	public Set<IProgramVar> getWrittenVars(final LOC loc) {
		return mWrittenSharedVars.get(loc);
	}

	public Set<IProgramVar> getReadVars(final ACTION action) {
		return mReadSharedVars.get(action);
	}

	public String getProcedureFromAction(final ACTION action) {
		return mAction2Procedure.get(action);
	}

	public String getProcedureFromLoc(final LOC loc) {
		return mLoc2Procedure.get(loc);
	}

	public Set<ACTION> getActionsToPatchInto(final ACTION readAction) {
		return mActionsToPatch.get(readAction);
	}

	public Set<Entry<LOC, Set<IProgramVar>>> getSharedWriteIterable() {
		return mWrittenSharedVars.entrySet();
	}

	public Set<Entry<ACTION, Set<IProgramVar>>> getSharedReadIterable() {
		return mReadSharedVars.entrySet();
	}

	public ACTION computeLoc2Action(final LOC loc) {
		return mLoc2Action.get(loc);
	}

	public boolean canReadFromInterference(final ACTION readAction, final LOC write) {
		final String intProcedure = mLoc2Procedure.get(write);
		return intProcedure.equals(getProcedureFromAction(readAction))
				|| mReadProcedures.get(readAction).contains(intProcedure);
	}

	public Map<LOC, DisjunctiveAbstractState<STATE>> filterProcedures(final String name,
			final Map<LOC, DisjunctiveAbstractState<STATE>> interferences) {
		// TODO: check nicer way via .collect ???
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
		interferences.entrySet().stream().filter(a -> mLoc2Procedure.get(a.getKey()) == (name))
				.forEach(b -> result.put(b.getKey(), b.getValue()));
		return result;
	}

	public Map<LOC, DisjunctiveAbstractState<STATE>> copyMap(final Map<LOC, DisjunctiveAbstractState<STATE>> map) {
		final Map<LOC, DisjunctiveAbstractState<STATE>> result = new HashMap<>();
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
			mReadProcedures.put(entry.getKey(), new HashSet<>());
		}

		// TODO: combine both iterations later
		for (final Entry<String, ? extends IcfgLocation> entry : entryNodes.entrySet()) {
			final IcfgEdgeIterator iterator = new IcfgEdgeIterator(entry.getValue().getOutgoingEdges());
			for (final var edge : iterator.asStream().collect(Collectors.toSet())) {
				if (edge instanceof IForkActionThreadCurrent) {
					final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
					addFork(entry.getValue().getProcedure(), fork.getNameOfForkedProcedure());
					addParallel(fork.getNameOfForkedProcedure(), entry.getValue().getProcedure());

					final IcfgEdgeIterator forkIterator = new IcfgEdgeIterator(edge);
					// skip first, as it is the fork Statement
					forkIterator.next();
					forkIterator.asStream().forEach(a -> checkforInterferences(a, fork.getNameOfForkedProcedure()));
				}
			}
		}

		closure(mForks);

		for (final var entry : mParallelProcedures.entrySet()) {
			final Set<String> tempSet = new HashSet<>();
			for (final var procedure : entry.getValue()) {
				//
				if (mForks.containsKey(procedure) && !procedure.equals("ULTIMATE.start")) {
					tempSet.addAll(mForks.get(procedure));
				}
			}
			tempSet.remove(entry.getKey());
			mParallelProcedures.get(entry.getKey()).addAll(tempSet);
		}

		for (final Entry<ACTION, Set<String>> entry : mReadProcedures.entrySet()) {
			// every Read that has xy in mReadProcedures gets all mForks.get(xy) added
			final Set<String> tempSet = new HashSet<>();
			for (final String procedure : entry.getValue()) {
				if (mForks.containsKey(procedure)) {
					tempSet.addAll(mForks.get(procedure));
				}
			}
			mReadProcedures.get(entry.getKey()).addAll(tempSet);

			// every Read in the procedure xy gets all mParallelProcedures.get(xy) added
			if (mParallelProcedures.containsKey(getProcedureFromAction(entry.getKey()))) {
				mReadProcedures.get(entry.getKey())
						.addAll(mParallelProcedures.get(getProcedureFromAction(entry.getKey())));
			}
		}

		final boolean timestop = true;
	}

	private static void closure(final Map<String, Set<String>> map) {
		boolean changes = true;
		while (changes) {
			changes = false;
			for (final Entry<String, Set<String>> entry : map.entrySet()) {
				final Set<String> tempSet = new HashSet<>();
				for (final String forked : entry.getValue()) {
					if (map.containsKey(forked)
							&& !DataStructureUtils.difference(map.get(forked), map.get(entry.getKey())).isEmpty()) {
						tempSet.addAll(map.get(forked));
						changes = true;
					}
				}
				map.get(entry.getKey()).addAll(tempSet);
			}
		}
	}

	private void readHandling(final IcfgEdge edge, final String forkProcedure) {
		if (mReadSharedVars.containsKey(edge)) {
			final Set<String> tempSet = mReadProcedures.get(edge);
			tempSet.add(forkProcedure);
			mReadProcedures.put((ACTION) edge, tempSet);
		}
	}

	private void checkforInterferences(final IcfgEdge edge, final String currentProcedure) {
		readHandling(edge, currentProcedure);

		if (edge instanceof IForkActionThreadCurrent) {
			// Procedures running parallel -> co-dependent
			final IForkActionThreadCurrent fork = (IForkActionThreadCurrent) edge;
			addParallel(currentProcedure, fork.getNameOfForkedProcedure());
			addParallel(fork.getNameOfForkedProcedure(), currentProcedure);
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

	private void addParallel(final String p1, final String p2) {
		final Set<String> tempSet;
		if (mParallelProcedures.containsKey(p1)) {
			tempSet = mParallelProcedures.get(p1);
		} else {
			tempSet = new HashSet<>();
		}
		tempSet.add(p2);
		mParallelProcedures.put(p1, tempSet);
	}

	private void computationsPerEdge(final String procedure, final IcfgEdge edge, final Set<IProgramVar> variables) {
		// SharedWrites & mProcedures
		boolean accepted = false;
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getAssignedVars(), variables)) {
			accepted = true;
			mWrittenSharedVars.put((LOC) edge.getSource(), new HashSet<>());
			edge.getTransformula().getAssignedVars().forEach(var -> mWrittenSharedVars.get(edge.getSource()).add(var));
			mLoc2Procedure.put((LOC) edge.getSource(), edge.getPrecedingProcedure());
			mLoc2Action.put((LOC) edge.getSource(), (ACTION) edge);
		}
		// SharedReads
		if (DataStructureUtils.haveNonEmptyIntersection(edge.getTransformula().getInVars().keySet(), variables)) {
			accepted = true;
			mReadSharedVars.put((ACTION) edge, new HashSet<>());
			mActionsToPatch.put((ACTION) edge, new HashSet<>());
			DataStructureUtils.intersection(edge.getTransformula().getInVars().keySet(), variables)
					.forEach(var -> mReadSharedVars.get(edge).add(var));
			edge.getSource().getIncomingEdges().forEach(a -> mActionsToPatch.get(edge).add((ACTION) a));
			mAction2Procedure.put((ACTION) edge, edge.getSource().getProcedure());
		}
	}
}
