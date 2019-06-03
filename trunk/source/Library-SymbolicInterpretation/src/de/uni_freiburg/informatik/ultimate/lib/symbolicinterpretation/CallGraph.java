/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-SymbolicInterpretation plug-in.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-SymbolicInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-SymbolicInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-SymbolicInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-SymbolicInterpretation plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.symbolicinterpretation;

import java.util.Collection;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

public class CallGraph {

	/**
	 * Temporary mark for {@link #mSuccessorsOfInterest} used in {@link #mark(String, String)} to detect
	 * cycles/recursion.
	 * <p>
	 * Cycle detection works as in Djikstra's DFS-based topological sorting, see
	 * <a href="https://en.wikipedia.org/wiki/Topological_sorting#Depth-first_search">Wikipedia</a>.
	 * <p>
	 * This mark has to be different from the usual marks. Usual marks are procedure names.
	 * Procedure names cannot be empty.
	 */
	private static final String TMP_MARK_TO_DETECT_CYCLES = "";

	private final IIcfg<IcfgLocation> mIcfg;

	/**
	 * Locations of interest (LOI) are locations inside procedures for which we want to compute predicates.
	 */
	private final HashRelation<String, IcfgLocation> mLOIsInsideProcedure = new HashRelation<>();

	/**
	 * Lists callers. This relation represents the call graph's directed edges backwards.
	 * <p>
	 * For procedures f, g: g Rel f iff f calls g.
	 */
	private final HashRelation<String, String> mPredecessors = new HashRelation<>();

	/**
	 * Lists callees which can be entered to reach a location of interest.
	 * <p>
	 * For procedures f, g: f Rel g iff f calls g and
	 * <ul>
	 * <li>g contains a location of interest
	 * <li><b>or</b> there is a procedure h such that g Rel h.
	 * </ul>
	 */
	private final HashRelation<String, String> mSuccessorsOfInterest = new HashRelation<>();

	public CallGraph(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		assignLOIsToProcedures(locationsOfInterest);
		buildGraph();
		markGraph();
	}

	private void assignLOIsToProcedures(final Collection<IcfgLocation> locationsOfInterest) {
		locationsOfInterest.forEach(loi -> mLOIsInsideProcedure.addPair(loi.getProcedure(), loi));
	}

	private void buildGraph() {
		new IcfgEdgeIterator(mIcfg).asStream()
				.filter(edge -> edge instanceof IIcfgCallTransition<?>)
				.forEach(this::addCall);
	}

	private void addCall(final IcfgEdge call) {
		mPredecessors.addPair(call.getTarget().getProcedure(), call.getSource().getProcedure());
	}

	private void markGraph() {
		mLOIsInsideProcedure.getDomain().stream().forEach(this::mark);
	}

	private void mark(final String currentProcedure) {
		if (!mSuccessorsOfInterest.addPair(currentProcedure, TMP_MARK_TO_DETECT_CYCLES)) {
			throw new IllegalArgumentException("Recursive programs are not supported.");
		}
		mPredecessors.getImage(currentProcedure).forEach(predecessor -> mark(predecessor, currentProcedure));
		mSuccessorsOfInterest.removePair(currentProcedure, TMP_MARK_TO_DETECT_CYCLES);
	}

	private void mark(final String currentProcedure, final String mark) {
		if (!mSuccessorsOfInterest.addPair(currentProcedure, mark)) {
			// Was already marked accordingly, therefore predecessors have to be already marked too.
			return;
		}
		mark(currentProcedure);
	}

	public Collection<String> initialProceduresOfInterest() {
		return mIcfg.getInitialNodes().stream()
				.map(IcfgLocation::getProcedure)
				.filter(procedure -> !mLOIsInsideProcedure.hasEmptyImage(procedure)
						|| !mSuccessorsOfInterest.hasEmptyImage(procedure))
				.collect(Collectors.toList());
	}

	public Set<IcfgLocation> locationsOfInterest(final String procedure) {
		return mLOIsInsideProcedure.getImage(procedure);
	}

	public Set<String> successorsOfInterest(final String procedure) {
		return mSuccessorsOfInterest.getImage(procedure);
	}
}






























