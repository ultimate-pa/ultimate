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

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.IdentityHashSet;

/**
 * Collect all formula labels used to prove unsatisfiability.
 * @author Juergen Christ
 */
public class UnsatCoreCollector {
	private final Script mScript;
	public UnsatCoreCollector(Script script) {
		mScript = script;
	}
	
	public Term[] getUnsatCore(Clause unsat) {
		try {
			final HashSet<String> unsatCoreIds = run(unsat);
			final Term[] res = new Term[unsatCoreIds.size()];
			int i = -1;
			for (final String s : unsatCoreIds) {
				res[++i] = mScript.term(s);
			}
			return res;
		} catch (final SMTLIBException ese) {
			throw new InternalError(ese.getMessage());
		}
	}

	private HashSet<String> run(Clause unsat) {
		final HashSet<String> res = new HashSet<String>();
		final ArrayDeque<Clause> todo = new ArrayDeque<Clause>();
		todo.push(unsat);
		final IdentityHashSet<Clause> visited = new IdentityHashSet<Clause>();
		while (!todo.isEmpty()) {
			final Clause c = todo.pop();
			if (visited.add(c)) {
				if (c.getProof().isLeaf()) {
					final LeafNode l = (LeafNode) c.getProof();
					// Tautologies are not needed in an unsat core
					if (l.getLeafKind() == LeafNode.NO_THEORY
							&& l.getTheoryAnnotation() instanceof SourceAnnotation) {
						final String name = ((SourceAnnotation) l.getTheoryAnnotation()).
							getAnnotation();
						// Guard against unnamed clauses
						if (!name.isEmpty()) {
							res.add(name);
						}
					}
				} else {
					final ResolutionNode n = (ResolutionNode) c.getProof();
					todo.push(n.getPrimary());
					final Antecedent[] ants = n.getAntecedents();
					for (final Antecedent a : ants) {
						todo.push(a.mAntecedent);
					}
				}
			}
		}
		return res;
	}
}
