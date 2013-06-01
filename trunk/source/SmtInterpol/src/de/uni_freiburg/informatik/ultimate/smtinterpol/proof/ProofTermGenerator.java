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
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * A non-recursive proof tree printer.  This class tries to avoid a stack
 * overflow by using an explicit stack that contains different visitors. 
 * @author Juergen Christ
 */
public class ProofTermGenerator {
	/**
	 * A very abstract base interface used for non-recursive operations.
	 * @author Juergen Christ
	 */
	private static interface Visitor {
		public void visit(ProofTermGenerator engine);
	}
	
	private static class GenerateTerm implements Visitor {
		private Clause m_Cls;
		public GenerateTerm(Clause cls) {
			assert cls.getProof() instanceof ResolutionNode;
			m_Cls = cls;
		}
		public void visit(ProofTermGenerator engine) {
			Theory t = engine.getTheory();
			Antecedent[] antes = ((ResolutionNode) m_Cls.getProof()).
					getAntecedents();
			Term[] args = new Term[1 + antes.length];
			args[0] = engine.getConverted();
			for (int i = 0; i < antes.length; ++i)
				args[i+1] = t.annotatedTerm(
						new Annotation[] {
								new Annotation(":pivot",
										antes[i].pivot.getSMTFormula(t, true))},
										engine.getConverted());
			Term res = t.term("@res", args);
			engine.setResult(m_Cls, res);
			engine.pushConverted(res);
		}
	}
	
	private static class Expander implements Visitor {
		private Clause m_Cls;
		public Expander(Clause cls) {
			m_Cls = cls;
		}
		public void visit(ProofTermGenerator engine) {
			Theory t = engine.getTheory();
			Term known = engine.getTerm(m_Cls);
			if (known != null) {
				engine.pushConverted(known);
				return;
			}
			ProofNode pn = m_Cls.getProof();
			if (pn.isLeaf()) {
				LeafNode ln = (LeafNode) pn;
				Term res;
				if (ln.getLeafKind() == LeafNode.EQ) {
					res = t.term("@tautology", t.annotatedTerm(new Annotation[] {
							ProofConstants.AUXANNOTS[ProofConstants.AUX_EQ]
					}, m_Cls.toTerm(t)));
				} else {
					IAnnotation annot = ln.getTheoryAnnotation();
					res = annot.toTerm(m_Cls, t);
				}
				engine.setResult(m_Cls, res);
				engine.pushConverted(res);
			} else {
				ResolutionNode rn = (ResolutionNode) pn;
				engine.enqueue(new GenerateTerm(m_Cls));
				engine.enqueue(new Expander(rn.getPrimary()));
				Antecedent[] antes = rn.getAntecedents();
				for (Antecedent ante : antes)
					engine.enqueue(new Expander(ante.antecedent));
			}
		}
	}
	/**
	 * The stack of pending visitors.
	 */
	private Deque<Visitor> m_Todo = new ArrayDeque<Visitor>();
	/**
	 * Enqueue a new visitor.
	 * @param visitor Visitor to enqueue.
	 */
	void enqueue(Visitor visitor) {
		m_Todo.push(visitor);
	}
	/**
	 * Process visitors until all are processed.
	 */
	private void run() {
		while (!m_Todo.isEmpty())
			m_Todo.pop().visit(this);
	}
	/**
	 * Stack of recently produced antecedent names.
	 */
	private Deque<Term> m_Converted = new ArrayDeque<Term>();
	/**
	 * Theory used in sexpr conversion.
	 */
	private Theory m_Theory;
	/**
	 * Mapping from clauses to terms representing the corresponding proof node.
	 */
	private Map<Clause, Term> m_Nodes = new HashMap<Clause, Term>();
	/**
	 * Initialize the generator with a theory.
	 * @param t   The theory.
	 */
	public ProofTermGenerator(Theory t) {
		m_Theory = t;
	}
	public Theory getTheory() {
		return m_Theory;
	}
	
	Term getTerm(Clause cls) {
		return m_Nodes.get(cls);
	}
	
	Term getConverted() {
		return m_Converted.pop();
	}
	
	void pushConverted(Term res) {
		assert(res.getSort().getName().equals("@Proof"));
		m_Converted.push(res);
	}
	
	void setResult(Clause cls, Term res) {
		m_Nodes.put(cls, res);
	}
	
	public Term convert(Clause cls) {
		assert cls.getSize() == 0;
		assert cls.getProof() != null;
		enqueue(new Expander(cls));
		run();
		Term res = m_Converted.pop();
		return SMTAffineTerm.cleanup(res);
	}
	
}
