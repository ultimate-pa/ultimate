/*
 * Copyright (C) 2009-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE Automata Library.
 *
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.petrinet.julian;

import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

public class ConditionEventsCoRelation<S, C> implements ICoRelation<S, C> {
	private int coRelationQueries = 0;

	private HashMap<Condition<S, C>, Set<Event<S, C>>> coRelation = new HashMap<Condition<S, C>, Set<Event<S, C>>>();
	private BranchingProcess<S, C> branchingProcess;

	@Override
	public int getCoRelationQueries() {
		return coRelationQueries;
	}

	public ConditionEventsCoRelation(BranchingProcess<S, C> branchingProcess) {
		this.branchingProcess = branchingProcess;
	}

	@Override
	public void update(Event<S, C> e) {
		for (Condition<S, C> c : e.getSuccessorConditions()) {
			coRelation.put(c, new HashSet<Event<S, C>>());
		}
		for (Event<S, C> e1 : branchingProcess.getEvents()) {
			if (isInIrreflexiveCoRelation(e, e1)) {
				for (Condition<S, C> c : e1.getSuccessorConditions()) {
					assert (!e.getPredecessorConditions().contains(c));
					assert (!e.getSuccessorConditions().contains(c));
					coRelation.get(c).add(e);
				}
			}
		}

		// Original plan: insert all siblings of predecessors of e, that are not
		// predecessors of e.
		// Problem: there is a situation where this might be incorrect.

		// Solution: only add Conditions that build a CoSet with the new Events
		// Predecessors.

		// Next Problem: this is incomplete.
		// There may be nodes, that are in co-relation with
		// the newly added Event e that are NOT siblings of
		// the predecessor-conditions of e.

		// Solution: iterate through all ancestors and do this
		
		/// (this is the old code)
		//for (Condition<S, C> c : e.getPredecessorConditions()) {
		//	for (Condition<S, C> sibling : c.getPredecessorEvent()
		//			.getSuccessorConditions()) {
		//		if (!e.getPredecessorConditions().contains(sibling)
		//				&& isCoset(e.getPredecessorConditions(), sibling)) {
		//			assert (!e.getSuccessorConditions().contains(sibling));
		//			coRelation.get(sibling).add(e);
		//		}
		//	}
		//}
		
		for (Condition<S, C> c : e.getConditionMark()) {
			if (!e.getSuccessorConditions().contains(c)) {
				assert (!e.getSuccessorConditions().contains(c));
				assert (!branchingProcess.inCausalRelation(c, e)) : c + " , "
						+ e + " in causal relation, not in co-relation!";
				coRelation.get(c).add(e);
			}
		}
	}

	// private void add(Condition<S, C> c, Event<S, C> e) {
	// Set<Event<S, C>> eSet = coRelation.get(c);
	// if (eSet == null) {
	// eSet = new HashSet<Event<S, C>>();
	// coRelation.put(c, eSet);
	// }
	// eSet.add(e);
	// }

	@Override
	public boolean isInCoRelation(Condition<S, C> c1, Condition<S, C> c2) {
		coRelationQueries++;
		boolean result = coRelation.get(c1).contains(c2.getPredecessorEvent())
				|| coRelation.get(c2).contains(c1.getPredecessorEvent())
				|| (c1.getPredecessorEvent() == c2.getPredecessorEvent());
		if (result) {
			assert (!branchingProcess.inCausalRelation(c1, c2)) : c1 + " , "
					+ c2 + " in causal relation, not in co-relation!";
			assert (!branchingProcess.inConflict(c1, c2)) : c1 + " , " + c2
					+ " in conflict, not in co-relation!";
		} else {
			assert (branchingProcess.inCausalRelation(c1, c2) || branchingProcess
					.inConflict(c1, c2)) : c1 + " , " + c2
					+ " missing in co-relation!";
		}
		return result;
	}

	/**
	 * <p>
	 * true, if both events are in irreflexive co-relation, hereafter "ic".
	 * </p>
	 * 
	 * <p>
	 * x ic y iif (x co y and x != y)
	 * </p>
	 * 
	 * <p>
	 * with *e i denote the predecessor-nodes of e.
	 * </p>
	 * 
	 * <p>
	 * 1. If e1 ic e2 then their parents are pairwise in irreflexive
	 * co-relation.<br>
	 * <b>Proof:</b> <br>
	 * let e1 co e2. Furthermore let ci be a predecessor of ei for i \in {1,2}
	 * </p>
	 * 
	 * <p>
	 * If c1#c2 then e1#e2 _|_.<br>
	 * If c1 and c2 are equal then e1#e2 or e1=e2 _|_.<br>
	 * If c1 and c2 are in causal relation, then one of the following must hold:
	 * e1 is in causal relation to e2 e1 # e2 _|_ <br>
	 * q.e.d.
	 * </p>
	 * 
	 * 
	 * <p>
	 * 2. If for all c1 \in *e1, c2 \in *e2: c1 ic c2 then e1 ci e2.<br>
	 * <b>Proof:</b>Assume the left side of the implication.
	 * </p>
	 * <p>
	 * If e1 = e2 it is trivial, that there are c1,c2 s.t. c1=c2 _|_<br>
	 * Assume e1 < e2, then there has to be a path between e1 and e2 s.t.
	 * \exists c1 \in *e1 s.t. c1 < e2. For each parent c2 \in *e2 then c1 < c2
	 * holds. (e1 > e2 analogously) _|_<br>
	 * Note: This is based on the assumption, that both Events have at least one
	 * predecessor-condition. <br>
	 * Assume e1#e2. There is a Condition c and Events e1', e2' \in c* s.t. e1'
	 * < e1 and e2' < e2. There is c1 \in *e1 s.t. either c1 < c or c1=c.<br>
	 * If e2 = e2' then c \in *e2 _|_ (e1=e1' analogously). <br>
	 * If e1 != e1' and e2 != e2' then there are predecessor-conditions c1 \in
	 * *e1, c2 \in *e2 s.t. c1#c2 _|_. <br>
	 * q.e.d.
	 * </p>
	 * 
	 * @param conditions
	 * @param e
	 * @return
	 */
	private boolean isInIrreflexiveCoRelation(Event<S, C> e1, Event<S, C> e2) {
		if (e1 == e2) // since this is irreflexive.
			return false;
		if (branchingProcess.getDummyRoot() == e1 
				|| branchingProcess.getDummyRoot() == e2 ) {
			return false;
		}
		Collection<Condition<S, C>> conditions1 = e1.getPredecessorConditions();
		Collection<Condition<S, C>> conditions2 = e2.getPredecessorConditions();
		for (Condition<S, C> c1 : conditions1) {
			if (conditions2.contains(c1) // e1 and e2 are in conflict
					|| !isCoset(conditions2, c1))
				return false;
		}
		return true;
	}

	@Override
	public void initialize(Set<Condition<S, C>> initialConditions) {
		// there are no events the conditions could be in relation with yet.
		// hence there's nothing to do here
	}

	@Override
	public boolean isCoset(Collection<Condition<S, C>> coSet, Condition<S, C> c) {
		for (Condition<S, C> condition : coSet) {
			if (!isInCoRelation(c, condition))
				return false;
		}
		return true;
	}

}
