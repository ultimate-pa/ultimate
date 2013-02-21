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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * Partially regularize a proof.  We regularize a proof by computing a set of
 * literals that are "safe" for this proof node.  A literal is "safe" if it is
 * either present in the node, or resolved on every path from that node to the
 * root of the proof.
 * 
 * We compute the set of safe literals and the nodes to regularize in one pass.
 * The method relies on the following facts about nodes of type
 * {@link ResolutionNode}:
 * <ul>
 * <li>A pivot can only occur once in the antecedent chain</li>
 * <li>A pivot can only occur in one polarity in the resolution chain</li>
 * </ul>
 * 
 * Given a {@link ResolutionNode} and a set of literals that are safe for the
 * result clause of that resolution node, we can compute the set of safe
 * literals for an antecedent by adding the negated pivots of all later
 * antecedents (those with bigger indices in the antecedent array) to the base
 * set of safe literals.
 * 
 * We can delete an antecedent clause if the corresponding pivot is safe.  This
 * removes the antecedent from the proof.  To remove multiple antecedents from
 * the resolution node, we mark the antecedent as removed.  This can be done if
 * the negation of the pivot is safe.  In this case, we replace the resolution
 * primary with the antecedent clause.
 * 
 * Storing the set of safe literals is unnecessary if the node has fan out 1.
 * Otherwise, we have to store the set of safe literals and build the
 * intersection of the safe literals of all paths.  In this context, we need to
 * adjust the counts of the clauses even if we remove a whole branch of the
 * proof tree (i.e., we mark an antecedent deleted).  We still need to visit all
 * nodes in the removed part of the proof tree to get correct counts.  But
 * instead of building the intersection with the already computed set of safe
 * literals, we only increment the counters and expand a node with fan out
 * greater than 1 when we visit it for the last time.
 * @author Juergen Christ
 */
public class RecyclePivots {
	/**
	 * Base interface for all workers used to regularize the proof.
	 * @author Juergen Christ
	 */
	private interface Worker {
		public void work();
	}

	/**
	 * Helper class that checks for possible regularizations in a sub proof
	 * w.r.t. a given set of safe literals for the root of the sub proof. 
	 * @author Juergen Christ
	 */
	private class SetAndExpand implements Worker {
		/**
		 * The root of the sub proof.
		 */
		Clause m_Cls;
		/**
		 * The set of literals safe for the root.
		 * This is null, if all literals are safe (because the
		 * clause is not reached in this path).
		 */
		Set<Literal> m_Safes;
		public SetAndExpand(Clause cls, Set<Literal> safes) {
			m_Cls = cls;
			m_Safes = safes;
		}
		
		@Override
		public void work() {
			if (seen(m_Cls)) {
				Set<Literal> oldSafes = m_SafeLits.get(m_Cls);
				if (m_Safes == null)
					m_Safes = oldSafes;
				else if (oldSafes != null)
					m_Safes.retainAll(oldSafes);
				
				// Clause has been seen for the last time.
				ProofNode pn = m_Cls.getProof();
				// We can skip leaf nodes since they cannot be regularized
				if (!pn.isLeaf()) {
					Set<Literal> delLits = null;
					ResolutionNode rn = (ResolutionNode) pn;
					Antecedent[] antes = rn.getAntecedents();
					for (int i = antes.length - 1; i >= 0; --i) {
						HashSet<Literal> newSafes = null;
						if (m_Safes == null) {
							// do nothing, visit sub nodes with null
						} else if (m_Safes.contains(antes[i].pivot.negate())) {
							// negation of pivot is safe =>
							// delete antecedent clause
							if (delLits == null)
								delLits = new HashSet<Literal>();
							delLits.add(antes[i].pivot);
							// visit antecedent with null since we do not use it.
						} else 	if (!antes[i].antecedent.getProof().isLeaf()) {
							// Sub proof is not a leaf => try to regularize
							// copy safes and add the pivot to get the 
							// new safes set for the antecedent.
							newSafes = new HashSet<Literal>(m_Safes);
							newSafes.add(antes[i].pivot);
						}
						
						if (!antes[i].antecedent.getProof().isLeaf()) {
							m_Todo.push(new SetAndExpand(
									antes[i].antecedent, newSafes));
						}

						if (m_Safes != null && 
							m_Safes.contains(antes[i].pivot)) {
							// pivot is safe => delete antecedent
							if (delLits == null)
								delLits = new HashSet<Literal>();
							delLits.add(antes[i].pivot.negate());
							m_Safes = null;
						}							
						if (m_Safes != null)
							m_Safes.add(antes[i].pivot.negate());
					}
					if (delLits != null)
						m_Deleted.put(m_Cls, delLits);
					// Handle primary
					if (!rn.getPrimary().getProof().isLeaf()) {
						HashSet<Literal> newSafes = null;
						if (m_Safes != null)
							newSafes = new HashSet<Literal>(m_Safes);
						m_Todo.push(new SetAndExpand(rn.getPrimary(), newSafes));
					}
				}
			} else if (m_Safes != null) {
				// There are still parts left where we can reach this clause.
				// Compute intersection of safe literals for the paths seen so
				// far
				Set<Literal> oldSafes = m_SafeLits.get(m_Cls);
				if (oldSafes == null)
					m_SafeLits.put(m_Cls, m_Safes);
				else
					oldSafes.retainAll(m_Safes);
			}
		}
	}
	/**
	 * The occurrence map.
	 */
	private Map<Clause, Integer> m_Counts;
	/**
	 * The todo stack.
	 */
	private Deque<Worker> m_Todo = new ArrayDeque<Worker>();
	/**
	 * Set of all clauses already visited.
	 */
	private HashMap<Clause, Integer> m_Seen;
	
	private HashMap<Object, Set<Literal>> m_SafeLits;
	
	private Map<Clause, Set<Literal>> m_Deleted;
	
	public Map<Clause, Set<Literal>> regularize(
			Clause proof, Map<Clause, Integer> counts) {
		m_Counts = counts;
		m_SafeLits = new HashMap<Object, Set<Literal>>();
		m_Deleted = new HashMap<Clause, Set<Literal>>();
		m_Seen = new HashMap<Clause, Integer>();
		Set<Literal> safe = new HashSet<Literal>();
		for (int i = 0; i < proof.getSize(); ++i)
			safe.add(proof.getLiteral(i));
		m_Todo.push(new SetAndExpand(proof, safe));
		run();
		return m_Deleted;
	}
	/**
	 * Process all clauses in a non-recursive way.
	 */
	private void run() {
		while (!m_Todo.isEmpty()) {
			Worker w = m_Todo.pop();
			w.work();
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
		Integer cnt = m_Seen.get(cls);
		int newcnt = cnt == null ? 1 : cnt + 1;
		m_Seen.put(cls, newcnt);
		int total = m_Counts.get(cls);
		assert (newcnt <= total);
		return total == newcnt;
	}
}
