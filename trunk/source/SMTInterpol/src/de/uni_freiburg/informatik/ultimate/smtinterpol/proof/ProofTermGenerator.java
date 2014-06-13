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
		private final Clause mCls;
		public GenerateTerm(Clause cls) {
			assert cls.getProof() instanceof ResolutionNode;
			mCls = cls;
		}
		public void visit(ProofTermGenerator engine) {
			Theory t = engine.getTheory();
			Antecedent[] antes = ((ResolutionNode) mCls.getProof()).
					getAntecedents();
			Term[] args = new Term[1 + antes.length];
			args[0] = engine.getConverted();
			for (int i = 0; i < antes.length; ++i)
				args[i + 1] = t.annotatedTerm(
						new Annotation[] {
							new Annotation(":pivot",
									antes[i].mPivot.getSMTFormula(t, true))},
									engine.getConverted());
			Term res = t.term("@res", args);
			engine.setResult(mCls, res);
			engine.pushConverted(res);
		}
	}
	
	private static class Expander implements Visitor {
		private final Clause mCls;
		public Expander(Clause cls) {
			mCls = cls;
		}
		public void visit(ProofTermGenerator engine) {
			Term known = engine.getTerm(mCls);
			if (known != null) {
				engine.pushConverted(known);
				return;
			}
			ProofNode pn = mCls.getProof();
			if (pn.isLeaf()) {
				LeafNode ln = (LeafNode) pn;
				Term res;
				Theory t = engine.getTheory();
				IAnnotation annot = ln.getTheoryAnnotation();
				res = annot.toTerm(mCls, t);
				engine.setResult(mCls, res);
				engine.pushConverted(res);
			} else {
				ResolutionNode rn = (ResolutionNode) pn;
				engine.enqueue(new GenerateTerm(mCls));
				engine.enqueue(new Expander(rn.getPrimary()));
				Antecedent[] antes = rn.getAntecedents();
				for (Antecedent ante : antes)
					engine.enqueue(new Expander(ante.mAntecedent));
			}
		}
	}
	/**
	 * The stack of pending visitors.
	 */
	private final Deque<Visitor> mTodo = new ArrayDeque<Visitor>();
	/**
	 * Enqueue a new visitor.
	 * @param visitor Visitor to enqueue.
	 */
	void enqueue(Visitor visitor) {
		mTodo.push(visitor);
	}
	/**
	 * Process visitors until all are processed.
	 */
	private void run() {
		while (!mTodo.isEmpty())
			mTodo.pop().visit(this);
	}
	/**
	 * Stack of recently produced antecedent names.
	 */
	private final Deque<Term> mConverted = new ArrayDeque<Term>();
	/**
	 * Theory used in sexpr conversion.
	 */
	private final Theory mTheory;
	/**
	 * Mapping from clauses to terms representing the corresponding proof node.
	 */
	private final Map<Clause, Term> mNodes = new HashMap<Clause, Term>();
	/**
	 * Initialize the generator with a theory.
	 * @param t   The theory.
	 */
	public ProofTermGenerator(Theory t) {
		mTheory = t;
	}
	public Theory getTheory() {
		return mTheory;
	}
	
	Term getTerm(Clause cls) {
		return mNodes.get(cls);
	}
	
	Term getConverted() {
		return mConverted.pop();
	}
	
	void pushConverted(Term res) {
		assert res.getSort().getName().equals("@Proof");
		mConverted.push(res);
	}
	
	void setResult(Clause cls, Term res) {
		mNodes.put(cls, res);
	}
	
	public Term convert(Clause cls) {
		assert cls.getSize() == 0;
		assert cls.getProof() != null;
		enqueue(new Expander(cls));
		run();
		Term res = mConverted.pop();
		return SMTAffineTerm.cleanup(res);
	}
	
}
