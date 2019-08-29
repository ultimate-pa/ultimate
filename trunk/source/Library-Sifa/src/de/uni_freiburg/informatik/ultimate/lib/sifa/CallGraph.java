/*
 * Copyright (C) 2019 Claus Schätzle (schaetzc@tf.uni-freiburg.de)
 * Copyright (C) 2019 University of Freiburg
 *
 * This file is part of the ULTIMATE Library-Sifa plug-in.
 *
 * The ULTIMATE Library-Sifa plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Library-Sifa plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Library-Sifa plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Library-Sifa plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE Library-Sifa plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.sifa;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfg;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgCallTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdge;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgEdgeIterator;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IcfgLocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.TopologicalSorter;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * Detects which procedures have to be interpreted to reach a given set of locations of interest (LOIs).
 * The call graph is only represented internally and cannot be accessed explicitly since we don't have to.
 *
 * @author schaetzc@tf.uni-freiburg.de
 */
public class CallGraph {

	private final IIcfg<IcfgLocation> mIcfg;

	/**
	 * Maps each procedure to the set of LOIs it contains directly.
	 * Locations of interest (LOI) are locations inside procedures for which we want to compute predicates.
	 * <p>
	 * The domain of this relation is the set of all procedures in the icfg.
	 */
	private final HashRelation<String, IcfgLocation> mLOIsInsideProcedure = new HashRelation<>();
	/**
	 * Lists callers. This relation represents the call graph's directed edges backwards.
	 * <p>
	 * For procedures f, g: g Rel f iff f calls g.
	 */
	private final HashRelation<String, String> mCalledBy = new HashRelation<>();
	/**
	 * Lists callers. This relation represents the call graph's directed edges forwards.
	 * <p>
	 * For procedures f, g: f Rel g iff f calls g.
	 */
	private final HashRelation<String, String> mCalls = new HashRelation<>();
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
	/**
	 * Relevant procedures in topological order.
	 * Procedure p is relevant iff p is in {@link #initialProceduresOfInterest()}
	 * or there is another relevant procedure calling p.
	 */
	private List<String> mTopsortRelevant;

	public CallGraph(final IIcfg<IcfgLocation> icfg, final Collection<IcfgLocation> locationsOfInterest) {
		mIcfg = icfg;
		assignLOIsToProcedures(locationsOfInterest);
		buildGraph();
		computeSuccOfInterest();
		topsortRelevant();
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
		final String caller = call.getSource().getProcedure();
		final String callee = call.getTarget().getProcedure();
		mCalledBy.addPair(callee, caller);
		mCalls.addPair(caller, callee);
	}

	private void computeSuccOfInterest() {
		mLOIsInsideProcedure.getDomain().stream().forEach(this::markPredecessors);
	}

	private void markPredecessors(final String currentProcedure) {
		mCalledBy.getImage(currentProcedure).stream()
				// If a proc. was already marked accordingly its predecessors have to be already marked too.
				.filter(predecessor -> mSuccessorsOfInterest.addPair(predecessor, currentProcedure))
				.forEach(this::markPredecessors);
	}

	private void topsortRelevant() {
		final Optional<List<String>> topologicalOrdering = new TopologicalSorter<>(mCalls::getImage)
				.topologicalOrdering(callClosure(initialProceduresOfInterest()));
		if (!topologicalOrdering.isPresent()) {
			throw new IllegalArgumentException("Recursive programs are not supported.");
		}
		mTopsortRelevant = topologicalOrdering.get();
	}

	/**
	 * Computes the smallest closed set under the {@link #mCalls} relation for a given set of procedure names.
	 * @param procedures Set S
	 * @return The smallest set S' ⊇ S such that ∀ e1,e2 : (e1∊S' ∧ e1 calls e2) → e2∊S'
	 */
	private Set<String> callClosure(final Collection<String> procedures) {
		final Deque<String> work = new ArrayDeque<>(procedures);
		final Set<String> closure = new HashSet<>();
		while (!work.isEmpty()) {
			final String next = work.remove();
			if (closure.add(next)) {
				work.addAll(mCalls.getImage(next));
			}
		}
		return closure;
	}

	public Collection<String> initialProceduresOfInterest() {
		return mIcfg.getInitialNodes().stream()
				.map(IcfgLocation::getProcedure)
				.filter(this::hasLoiOrSuccessorWithLoi)
				.collect(Collectors.toList());
	}

	private boolean hasLoiOrSuccessorWithLoi(final String procedure) {
		return !mLOIsInsideProcedure.hasEmptyImage(procedure)
				|| !mSuccessorsOfInterest.hasEmptyImage(procedure);
	}

	public Set<IcfgLocation> locationsOfInterest(final String procedure) {
		return mLOIsInsideProcedure.getImage(procedure);
	}

	public Set<String> successorsOfInterest(final String procedure) {
		return mSuccessorsOfInterest.getImage(procedure);
	}

	public List<String> relevantProceduresTopsorted() {
		return mTopsortRelevant;
	}
}
