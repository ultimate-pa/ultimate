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
		private final Clause mCls;
		/**
		 * Set the clause to collect.
		 * @param cls The clause to collect.
		 */
		public CollectClause(Clause cls) {
			mCls = cls;
		}
		@Override
		public void process(FixProofDAG engine) {
			final ResolutionNode rn = (ResolutionNode) mCls.getProof();
			// Simplify rn
			final Set<Literal> removed = engine.mDeletedNodes.get(mCls);
			final Antecedent[] antes = rn.getAntecedents();
			final ArrayDeque<Antecedent> newAntes = 
					new ArrayDeque<ResolutionNode.Antecedent>();
			boolean deleted = false;
			boolean changed = false;
			
			Clause primary = null;
		newprimary:
		    {
				for (int i = antes.length - 1; i >= 0; --i) {
					if (removed != null) {
						if (removed.contains(antes[i].mPivot)) {
							// Antecedent has been removed
							changed = true;
							continue;
						}
						deleted = removed.contains(antes[i].mPivot.negate());
					}
					
					final Clause cls = engine.mTransformed.get(antes[i].mAntecedent);
					if (deleted || !cls.contains(antes[i].mPivot)) {
						primary = cls;
						changed = true;
						break newprimary;
					}
					
					if (cls == antes[i].mAntecedent) {
						newAntes.addFirst(antes[i]);
					} else {
						newAntes.addFirst(new Antecedent(antes[i].mPivot, cls));
						changed = true;
					}	
				}
				primary = engine.mTransformed.get(rn.getPrimary());
				changed |= primary != rn.getPrimary();
			}
			if (changed) {
				// recompute clause
				final HashSet<Literal> lits = new HashSet<Literal>();
				for (int i = 0; i < primary.getSize(); ++i) {
					lits.add(primary.getLiteral(i));
				}
				for (final Iterator<Antecedent> it = newAntes.iterator(); it.hasNext(); ) {
					final Antecedent a = it.next();
					final boolean resolutionStepUsed = lits.remove(a.mPivot.negate());
					if (!resolutionStepUsed) {
						it.remove();
						continue;
					}
					for (int j = 0; j < a.mAntecedent.getSize(); ++j) {
						final Literal lit = a.mAntecedent.getLiteral(j);
						if (lit != a.mPivot) {
							lits.add(lit);
						}
					}
				}
				Clause result;
				if (newAntes.isEmpty()) {
					result = primary;
				} else {
					final Antecedent[] nantes = newAntes.toArray(
						new Antecedent[newAntes.size()]);
					result = new Clause(lits.toArray(new Literal[lits.size()]),
						new ResolutionNode(primary, nantes));
				}
				engine.mTransformed.put(mCls, result);
			} else {
				engine.mTransformed.put(mCls, mCls);
			}
		}
		@Override
		public String toString() {
			return "Collect: " + mCls.toString();
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
		private final Clause mCls;
		/**
		 * Set the clause to expand.
		 * @param cls The clause to expand.
		 */
		public ExpandClause(Clause cls) {
			mCls = cls;
		}
		
		@Override
		public void process(FixProofDAG engine) {
			if (engine.mTransformed.containsKey(mCls)) {
				return;
			}
			final Set<Literal> removed = engine.mDeletedNodes.get(mCls);
			final ProofNode pn = mCls.getProof();
			if (pn.isLeaf()) {
				// m_Cls stays unchanged
				engine.mTransformed.put(mCls, mCls);
			} else {
				final ResolutionNode rn = (ResolutionNode) pn;
				engine.mTodo.push(new CollectClause(mCls));
				final Antecedent[] antes = rn.getAntecedents();
				boolean deleted = false;
				for (int i = antes.length - 1; !deleted && i >= 0; --i) {
					if (removed != null) {
						if (removed.contains(antes[i].mPivot)) {
							// Antecedent has been removed
							continue;
						}
						deleted = removed.contains(antes[i].mPivot.negate());
					}
					engine.mTodo.push(new ExpandClause(antes[i].mAntecedent));
				}
				if (!deleted) {
					engine.mTodo.push(new ExpandClause(rn.getPrimary()));
				}
			}
		}
		@Override
		public String toString() {
			return "Expand: " + mCls.toString();
		}
	}
	/**
	 * The todo stack.
	 */
	private final Deque<Worker> mTodo = new ArrayDeque<Worker>();
	/**
	 * Mapping for input to replaced clauses.
	 */
	private HashMap<Clause, Clause> mTransformed =
		new HashMap<Clause, Clause>();
	/**
	 * The set of deleted nodes.  This can either be clauses or antecedents
	 * which are used to represent the result of a resolution step.
	 */
	private Map<Clause, Set<Literal>> mDeletedNodes;
	/**
	 * Clear the transformation cache.
	 */
	public void reset() {
		mTransformed = new HashMap<Clause, Clause>();
	}
	/**
	 * Fix a proof tree rooted at <code>rt</code>.  Note that <code>rt</code>
	 * cannot be deleted for this algorithm to work properly.
	 * @param rt           The root of the proof tree to fix.
	 * @param deletedNodes The deleted nodes of the proof tree.
	 * @return A new proof tree with all removed nodes replaced.
	 */
	public Clause fix(Clause rt, Map<Clause, Set<Literal>> deletedNodes) {
		mDeletedNodes = deletedNodes;
		mTodo.push(new ExpandClause(rt));
		run();
		return mTransformed.get(rt);
	}
	/**
	 * Non-recursive walk over the proof tree and process the nodes.
	 */
	private final void run() {
		while (!mTodo.isEmpty()) {
			final Worker w = mTodo.pop();
			w.process(this);
		}
	}
}
