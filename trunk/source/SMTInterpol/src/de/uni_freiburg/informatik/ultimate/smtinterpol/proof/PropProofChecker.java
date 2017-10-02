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
import java.util.HashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Literal;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * A proof checker for the propositional structure of a proof.  This class only
 * checks the resolution chain.
 * @author Juergen Christ
 */
public class PropProofChecker {
	/**
	 * The list of clauses still to resolve.
	 */
	private final ArrayDeque<Clause> mTodo = new ArrayDeque<Clause>();
	/**
	 * The set of clauses that contain a valid proof.
	 */
	private final HashSet<Clause> mVisited = new HashSet<Clause>();
	public boolean check(Clause refutation) {
		mTodo.add(refutation);
		return run();
	}
	
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private boolean run() {
		int errors = 0;
		while (!mTodo.isEmpty()) {
			final Clause clause = mTodo.removeLast();
			if (!mVisited.contains(clause)) {
				final ProofNode pn = clause.getProof();
				if (pn.isLeaf()) {
					// I assume all leaves are correct!
					mVisited.add(clause);
				} else {
					final Antecedent[] antes = ((ResolutionNode) pn).getAntecedents();
					final Clause prim = ((ResolutionNode) pn).getPrimary();
					boolean unknownChild = false;
					if (!mVisited.contains(prim)) {
						if (!unknownChild) {
							// We add ourselves in front of all unknown
							// children to be reevaluated after they have
							// been processed.
							mTodo.addLast(clause);
						}
						unknownChild = true;
						mTodo.addLast(prim);
					}
					for (final Antecedent ante : antes) {
						if (!mVisited.contains(ante.mAntecedent)) {
							if (!unknownChild) {
								// We add ourselves in front of all unknown
								// children to be reevaluated after they have
								// been processed.
								mTodo.addLast(clause);
							}
							unknownChild = true;
							mTodo.addLast(ante.mAntecedent);
						}
					}
					if (!unknownChild) {
						// All children were known to be correct => check clause
						final HashSet<Literal> clauselits = new HashSet<Literal>();
						for (int i = 0; i < prim.getSize(); ++i) {
							clauselits.add(prim.getLiteral(i));
						}
						for (final Antecedent ante : antes) {
							final Clause antecls = ante.mAntecedent;
							if (!antecls.contains(ante.mPivot)) {
								System.err.println("Pivot literal "
										+ ante.mPivot + " not in antecedent");
								return false;
							}
							if (!clauselits.remove(ante.mPivot.negate())) {
								System.err.println("Negated pivot literal " 
										+ ante.mPivot.negate()
										+ " not in primary");
								return false;
							}
							for (int i = 0; i < antecls.getSize(); ++i) {
								final Literal lit = antecls.getLiteral(i);
								if (lit != ante.mPivot) {
									clauselits.add(lit);
								}
							}
						}
						// Here, we have done all resolution steps.  Check the
						// resulting clause
						final HashSet<Literal> clslits = new HashSet<Literal>();
						for (int i = 0; i < clause.getSize(); ++i) {
							clslits.add(clause.getLiteral(i));
						}
						if (!clauselits.equals(clslits)) {
							errors++;
							System.err.println("Result of resolution incorrect for: " + clause);
							final Set<Literal> clauseremain = (Set)clauselits.clone();
							clauseremain.removeAll(clslits);
							if (!clauseremain.isEmpty()) {
								System.err.println();
								System.err.println("Result misses:");
								System.err.println(clauseremain);
							}
							final Set<Literal> clsremain = (Set)clslits.clone();
							clsremain.removeAll(clauselits);
							if (!clsremain.isEmpty()) {
								System.err.println();
								System.err.println("Result additionally has:");
								System.err.println(clsremain);
							}
						}
						mVisited.add(clause);
					}
				}
			}
		}
		return errors == 0;
	}
}
