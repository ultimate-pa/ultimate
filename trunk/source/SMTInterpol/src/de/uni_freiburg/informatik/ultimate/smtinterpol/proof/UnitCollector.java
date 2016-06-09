/*
 * Copyright (C) 2009-2012 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import java.util.ArrayDeque;
import java.util.Deque;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Queue;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * Collect all units in a proof tree that occur more than once.  This is
 * accomplished by a DAG traversal of the proof tree.  If we see a node for the
 * last time, we visit it (i.e., add it to the unit queue if it is a unit clause
 * that occurs more than once) and visit the children. 
 * @author Juergen Christ
 */
public class UnitCollector {
	/**
	 * The occurrence map.
	 */
	private Map<Clause, Integer> mCounts;
	/**
	 * The collected unit clauses.
	 */
	private Queue<Antecedent> mUnits;
	/**
	 * The todo stack.
	 */
	private final Deque<Clause> mTodo = new ArrayDeque<Clause>();
	/**
	 * Set of all clauses already visited.
	 */
	private HashMap<Clause, Integer> mSeen;
	/**
	 * Mapping of all root clauses to a set of unit literals.  This is needed to
	 * create the map of the deleted nodes per context.
	 */
	private HashMap<Clause, Set<Literal>> mDelUnits;
	/**
	 * Collect all unit clauses that occur more than once in the proof tree
	 * rooted at <code>unsat</code>.
	 * @param unsat  Root of the proof tree.
	 * @param counts Clause counters.
	 * @return Unit clauses in bottom-up order.
	 */
	public Queue<Antecedent> collectUnits(
			Clause unsat, Map<Clause, Integer> counts) {
		mCounts = counts;
		mDelUnits = new HashMap<Clause, Set<Literal>>();
		mUnits = new ArrayDeque<Antecedent>();
		mSeen = new HashMap<Clause, Integer>();
		mTodo.push(unsat);
		run();
		return mUnits;
	}
	/**
	 * Process all clauses in a non-recursive way.
	 */
	private void run() {
		while (!mTodo.isEmpty()) {
			final Clause cls = mTodo.pop();
			if (seen(cls)) {
				if (cls.getSize() == 1 && mCounts.get(cls) > 1) {
					// Unit with at least two children
					mUnits.add(new Antecedent(cls.getLiteral(0), cls));
				}
				final ProofNode pn = cls.getProof();
				if (!pn.isLeaf()) {
					Set<Literal> deletions = null;
					// Enqueue children
					final ResolutionNode rn = (ResolutionNode) pn;
					final Antecedent[] antes = rn.getAntecedents();
					for (int i = antes.length - 1; i >= 0; --i) {
						if (antes[i].mAntecedent.getSize() == 1 
								&& mCounts.get(antes[i].mAntecedent) > 1) {
							// We will lower this unit => Mark it deleted
							if (deletions == null) {
								deletions = new HashSet<Literal>();
							}
							deletions.add(antes[i].mPivot);
						}
						mTodo.push(antes[i].mAntecedent);
					}
					mTodo.push(rn.getPrimary());
					if (deletions != null) {
						mDelUnits.put(cls, deletions);
					}
				}
			}
		}
	}
	/**
	 * Record that a clause is reached on a path through the DAG.  Returns
	 * <code>true</code> if and only if the clause is reached through the last
	 * path in the DAG that can reach this path.
	 * @param cls The clause just reached.
	 * @return Is this clause reached for the last time?
	 */
	private boolean seen(Clause cls) {
		final Integer cnt = mSeen.get(cls);
		final int newcnt = cnt == null ? 1 : cnt + 1;
		mSeen.put(cls, newcnt);
		final int total = mCounts.get(cls);
		assert (newcnt <= total);
		return total == newcnt;
	}
	/**
	 * Get the list of deleted nodes.  This map stores for every result of an
	 * ordered hyper resolution step the literals that occur as units in a
	 * resolution step.
	 * @return Deleted nodes per context.
	 */
	public Map<Clause, Set<Literal>> getDeletedNodes() {
		return mDelUnits;
	}
}
