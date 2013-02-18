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
	private ArrayDeque<Clause> m_Todo = new ArrayDeque<Clause>();
	/**
	 * The set of clauses that contain a valid proof.
	 */
	private HashSet<Clause> m_Correct = new HashSet<Clause>();
	public boolean check(Clause refutation) {
		m_Todo.add(refutation);
		return run();
	}
	
	@SuppressWarnings({ "rawtypes", "unchecked" })
	private boolean run() {
		while (!m_Todo.isEmpty()) {
			Clause clause = m_Todo.removeLast();
			if (!m_Correct.contains(clause)) {
				ProofNode pn = clause.getProof();
				if (pn.isLeaf())
					// I assume all leaves are correct!
					m_Correct.add(clause);
				else {
					Antecedent[] antes = ((ResolutionNode) pn).getAntecedents();
					Clause prim = ((ResolutionNode) pn).getPrimary();
					boolean unknownChild = false;
					if (!m_Correct.contains(prim)) {
						if (!unknownChild)
							// We add ourselves in front of all unknown
							// children to be reevaluated after they have
							// been processed.
							m_Todo.addLast(clause);
						unknownChild = true;
						m_Todo.addLast(prim);
					}
					for (Antecedent ante : antes) {
						if (!m_Correct.contains(ante.antecedent)) {
							if (!unknownChild)
								// We add ourselves in front of all unknown
								// children to be reevaluated after they have
								// been processed.
								m_Todo.addLast(clause);
							unknownChild = true;
							m_Todo.addLast(ante.antecedent);
						}
					}
					if (!unknownChild) {
						// All children were known to be correct => check clause
						HashSet<Literal> clauselits = new HashSet<Literal>();
						for (int i = 0; i < prim.getSize(); ++i)
							clauselits.add(prim.getLiteral(i));
						for (Antecedent ante : antes) {
							Clause antecls = ante.antecedent;
							if (!antecls.contains(ante.pivot)) {
								System.err.println("Pivot literal " +
										ante.pivot + " not in antecedent");
								return false;
							}
							if (!clauselits.remove(ante.pivot.negate())) {
								System.err.println("Negated pivot literal " + 
										ante.pivot.negate() +
										" not in primary");
								return false;
							}
							for (int i = 0; i < antecls.getSize(); ++i) {
								Literal lit = antecls.getLiteral(i);
								if (lit != ante.pivot)
									clauselits.add(lit);
							}
						}
						// Here, we have done all resolution steps.  Check the
						// resulting clause
						HashSet<Literal> clslits = new HashSet<Literal>();
						for (int i = 0; i < clause.getSize(); ++i)
							clslits.add(clause.getLiteral(i));
						if (clauselits.containsAll(clslits) &&
								clslits.containsAll(clauselits))
							m_Correct.add(clause);
						else {
							System.err.println("Result of resolution incorrect");
							System.err.println();
							System.err.println("Result misses:");
							Set<Literal> clauseremain = (Set)clauselits.clone();
							clauseremain.removeAll(clslits);
							System.err.println(clauseremain);
							System.err.println();
							System.err.println("Result additionally has:");
							Set<Literal> clsremain = (Set)clslits.clone();
							clsremain.removeAll(clauselits);
							System.err.println(clsremain);
							return false;
						}
					}
				}
			}
		}
//		System.err.println("Proof propositionally correct!");
		return true;
	}
}
