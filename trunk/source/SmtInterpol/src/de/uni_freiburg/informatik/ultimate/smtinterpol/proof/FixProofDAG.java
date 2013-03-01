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
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * Fix a proof tree by replacing deleted nodes.  We mark for the result of every
 * ordered binary hyperresolution (aka {@link ResolutionNode}) which literals
 * can be removed from this resolution.  If this list contains a literal on the
 * main path (i.e., the negation of a pivot stored in some resolution), it is
 * assumed to contain all literals from that point upwards the hyperresolution
 * chain.
 * @author Juergen Christ
 */
public class FixProofDAG {
	/**
	 * A work unit in the fixing process.
	 * @author Juergen Christ
	 */
	private static interface Worker {
		public void process(FixProofDAG engine);
	}
	/**
	 * Collect the transformed resolution proof for a clause.
	 * @author Juergen Christ
	 */
	private static class CollectClause implements Worker {
		/**
		 * The clause to collect.
		 */
		private Clause m_Cls;
		/**
		 * Set the clause to collect.
		 * @param cls The clause to collect.
		 */
		public CollectClause(Clause cls) {
			m_Cls = cls;
		}
		@Override
		public void process(FixProofDAG engine) {
			ResolutionNode rn = (ResolutionNode) m_Cls.getProof();
			// Simplify rn
			Set<Literal> removed = engine.m_DeletedNodes.get(m_Cls);
			Antecedent[] antes = rn.getAntecedents();
			ArrayDeque<Antecedent> newAntes = 
					new ArrayDeque<ResolutionNode.Antecedent>();
			boolean deleted = false;
			boolean changed = false;
			
			Clause primary = null;
			newprimary: {
				for (int i = antes.length - 1; i >= 0; --i) {
					if (removed != null) {
						if (removed.contains(antes[i].pivot)) {
							// Antecedent has been removed
							changed = true;
							continue;
						}
						deleted = removed.contains(antes[i].pivot.negate());
					}
					
					Clause cls = engine.m_Transformed.get(antes[i].antecedent);
					if (deleted || !cls.contains(antes[i].pivot)) {
						primary = cls;
						changed = true;
						break newprimary;
					}
					
					if (cls != antes[i].antecedent) {
						newAntes.addFirst(new Antecedent(antes[i].pivot, cls));
						changed = true;
					} else
						newAntes.addFirst(antes[i]);
				}
				primary = engine.m_Transformed.get(rn.getPrimary());
				changed |= primary != rn.getPrimary();
			}
			if (!changed)
				engine.m_Transformed.put(m_Cls, m_Cls);
			else {
				// recompute clause
				HashSet<Literal> lits = new HashSet<Literal>();
				for (int i = 0; i < primary.getSize(); ++i)
					lits.add(primary.getLiteral(i));
				for (Iterator<Antecedent> it = newAntes.iterator(); it.hasNext(); ) {
					Antecedent a = it.next();
					boolean resolutionStepUsed = lits.remove(a.pivot.negate());
					if (!resolutionStepUsed) {
						it.remove();
						continue;
					}
					for (int j = 0; j < a.antecedent.getSize(); ++j) {
						Literal lit = a.antecedent.getLiteral(j);
						if (lit != a.pivot)
							lits.add(lit);
					}
				}
				Clause result;
				if (newAntes.isEmpty()) {
					result = primary;
				} else {
					Antecedent[] nantes = newAntes.toArray(
						new Antecedent[newAntes.size()]);
					result = new Clause(lits.toArray(new Literal[lits.size()]),
						new ResolutionNode(primary, nantes));
				}
				engine.m_Transformed.put(m_Cls, result);
			}
		}
		public String toString() {
			return "Collect: " + m_Cls.toString();
		}
	}
	/**
	 * Expands the node in the proof DAG represented by a given clause.
	 * @author Juergen Christ
	 */
	private static class ExpandClause implements Worker {
		/**
		 * The clause to expand.
		 */
		private Clause m_Cls;
		/**
		 * Set the clause to expand.
		 * @param cls The clause to expand.
		 */
		public ExpandClause(Clause cls) {
			m_Cls = cls;
		}
		
		@Override
		public void process(FixProofDAG engine) {
			if (engine.m_Transformed.containsKey(m_Cls))
				return;
			Set<Literal> removed = engine.m_DeletedNodes.get(m_Cls);
			ProofNode pn = m_Cls.getProof();
			if (!pn.isLeaf()) {
				ResolutionNode rn = (ResolutionNode) pn;
				engine.m_Todo.push(new CollectClause(m_Cls));
				Antecedent[] antes = rn.getAntecedents();
				boolean deleted = false;
				for (int i = antes.length - 1; !deleted && i >= 0; --i) {
					if (removed != null) {
						if (removed.contains(antes[i].pivot))
							// Antecedent has been removed
							continue;
						deleted = removed.contains(antes[i].pivot.negate());
					}
					engine.m_Todo.push(new ExpandClause(antes[i].antecedent));
				}
				if (!deleted)
					engine.m_Todo.push(new ExpandClause(rn.getPrimary()));
			} else
				// m_Cls stays unchanged
				engine.m_Transformed.put(m_Cls, m_Cls);
		}
		public String toString() {
			return "Expand: " + m_Cls.toString();
		}
	}
	/**
	 * The todo stack.
	 */
	private Deque<Worker> m_Todo = new ArrayDeque<Worker>();
	/**
	 * Mapping for input to replaced clauses.
	 */
	private HashMap<Clause, Clause> m_Transformed =
		new HashMap<Clause, Clause>();
	/**
	 * The set of deleted nodes.  This can either be clauses or antecedents
	 * which are used to represent the result of a resolution step.
	 */
	private Map<Clause, Set<Literal>> m_DeletedNodes;
	/**
	 * Clear the transformation cache.
	 */
	public void reset() {
		m_Transformed = new HashMap<Clause, Clause>();
	}
	/**
	 * Fix a proof tree rooted at <code>rt</code>.  Note that <code>rt</code>
	 * cannot be deleted for this algorithm to work properly.
	 * @param rt           The root of the proof tree to fix.
	 * @param deletedNodes The deleted nodes of the proof tree.
	 * @return A new proof tree with all removed nodes replaced.
	 */
	public Clause fix(Clause rt, Map<Clause, Set<Literal>> deletedNodes) {
		m_DeletedNodes = deletedNodes;
		m_Todo.push(new ExpandClause(rt));
		run();
		return m_Transformed.get(rt);
	}
	/**
	 * Non-recursive walk over the proof tree and process the nodes.
	 */
	private final void run() {
		while (!m_Todo.isEmpty()) {
			Worker w = m_Todo.pop();
			w.process(this);
		}
	}
}
