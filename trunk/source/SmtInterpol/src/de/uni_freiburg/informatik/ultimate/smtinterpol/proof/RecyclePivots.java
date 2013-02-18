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
				if (oldSafes != null)
					m_Safes.retainAll(oldSafes);
				// Clause has been seen for the last time.
				ProofNode pn = m_Cls.getProof();
				// We can skip leaf nodes since they cannot be regularized
				if (!pn.isLeaf()) {
					Set<Literal> delLits = null;
					ResolutionNode rn = (ResolutionNode) pn;
					Antecedent[] antes = rn.getAntecedents();
					// Flag to mark the deletion of an antecedent
					// If true, we should only visit the rest without trying to
					// regularize anything
					boolean deleted = false;
					for (int i = antes.length - 1; i >= 0; --i) {
						if (deleted) {
							m_Todo.push(new Visitor(antes[i].antecedent));
							// delLits is not null here since we already deleted
							// a literal
							delLits.add(antes[i].pivot.negate());
						} else {
							if (m_Safes.contains(antes[i].pivot.negate())) {
								// negation of pivot is safe =>
								// delete antecedent clause
								if (delLits == null)
									delLits = new HashSet<Literal>();
								delLits.add(antes[i].pivot);
								// Only visit the subtree to get correct counts
								m_Todo.push(new Visitor(antes[i].antecedent));
							} else if (m_Safes.contains(antes[i].pivot)) {
								// pivot is safe => delete antecedent
								if (delLits == null)
									delLits = new HashSet<Literal>();
								delLits.add(antes[i].pivot.negate());
								deleted = true;
							} else if (
									!antes[i].antecedent.getProof().isLeaf()) {
								// Sub proof is not a leaf => try to regularize
								HashSet<Literal> safes =
									new HashSet<Literal>(m_Safes);
								safes.add(antes[i].pivot);
								m_Todo.push(
										new SetAndExpand(
												antes[i].antecedent, safes));
							}
							m_Safes.add(antes[i].pivot.negate());
						}
					}
					if (delLits != null)
						m_Deleted.put(m_Cls, delLits);
					// Handle primary
					if (deleted)
						m_Todo.push(new Visitor(rn.getPrimary()));
					else if (!rn.getPrimary().getProof().isLeaf()) {
						HashSet<Literal> safes = new HashSet<Literal>(m_Safes);
						for (Antecedent a : rn.getAntecedents())
							safes.add(a.pivot.negate());
						m_Todo.push(new SetAndExpand(rn.getPrimary(), safes));
					}
				}
			} else {
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
	 * Helper class used when an antecedent gets deleted.  This class only
	 * visits sub proofs without computing safe literals.  Once a node in the
	 * proof tree with fan out greater than 1 is visited for the last time, it
	 * starts the regularization again.
	 * @author Juergen Christ
	 */
	private class Visitor implements Worker {
		/**
		 * The root of the sub proof to visit.
		 */
		Clause m_Cls;
		public Visitor(Clause cls) {
			m_Cls = cls;
		}
		@Override
		public void work() {
			ProofNode pn = m_Cls.getProof();
			// We can skip leaves since the cannot be regularized
			if (!pn.isLeaf()) {
				Integer seen = m_Seen.get(m_Cls);
				int nseen = seen == null ? 1 : seen + 1;
				int total = m_Counts.get(m_Cls);
				if (total == nseen) {
					// We see it for the last time
					if (total > 1)
						// It is fan out > 1
						// Don't adjust the seen counter since SetAndExpand will
						// do this again
						m_Todo.push(new SetAndExpand(m_Cls,
								m_SafeLits.get(m_Cls)));
					else {
						// Increment the usage counter and expand the node
						m_Seen.put(m_Cls, nseen);
						ResolutionNode rn = (ResolutionNode) pn;
						m_Todo.push(new Visitor(rn.getPrimary()));
						for (Antecedent ante : rn.getAntecedents())
							m_Todo.push(new Visitor(ante.antecedent));
					}
				} else
					// Increment the usage counter
					m_Seen.put(m_Cls, nseen);
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
