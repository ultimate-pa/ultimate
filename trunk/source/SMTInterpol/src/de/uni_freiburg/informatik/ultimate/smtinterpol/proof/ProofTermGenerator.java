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
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.proof.ResolutionNode.Antecedent;

/**
 * A non-recursive proof tree printer.  This class tries to avoid a stack
 * overflow by using an explicit stack that contains different visitors.
 * @author Juergen Christ
 */
public class ProofTermGenerator extends NonRecursive {

	private static class GenerateTerm implements Walker {
		private final Clause mCls;
		public GenerateTerm(final Clause cls) {
			assert cls.getProof() instanceof ResolutionNode;
			mCls = cls;
		}
		@Override
		public void walk(final NonRecursive nr) {
			final ProofTermGenerator engine = (ProofTermGenerator) nr;
			final Theory t = engine.getTheory();
			final Antecedent[] antes = ((ResolutionNode) mCls.getProof()).
					getAntecedents();
			final Term[] args = new Term[1 + antes.length];
			args[0] = engine.getConverted();
			for (int i = 0; i < antes.length; ++i) {
				args[i + 1] = t.annotatedTerm(
						new Annotation[] {
							new Annotation(":pivot",
									antes[i].mPivot.getSMTFormula(t, true))},
									engine.getConverted());
			}
			final Term res = t.term("@res", args);
			engine.setResult(mCls, res);
			engine.pushConverted(res);
		}
	}

	private static class Expander implements Walker {
		private final Clause mCls;
		public Expander(final Clause cls) {
			mCls = cls;
		}
		@Override
		public void walk(final NonRecursive nr) {
			final ProofTermGenerator engine = (ProofTermGenerator) nr;
			final Term known = engine.getTerm(mCls);
			if (known != null) {
				engine.pushConverted(known);
				return;
			}
			final ProofNode pn = mCls.getProof();
			if (pn.isLeaf()) {
				final LeafNode ln = (LeafNode) pn;
				Term res;
				final Theory t = engine.getTheory();
				final IAnnotation annot = ln.getTheoryAnnotation();
				if (annot == null) {
					assert ln.getLeafKind() == LeafNode.ASSUMPTION;
					res = t.term("@assumption", mCls.toTerm(t));
				} else {
					res = annot.toTerm(mCls, t);
				}
				engine.setResult(mCls, res);
				engine.pushConverted(res);
			} else {
				final ResolutionNode rn = (ResolutionNode) pn;
				engine.enqueueWalker(new GenerateTerm(mCls));
				engine.enqueueWalker(new Expander(rn.getPrimary()));
				final Antecedent[] antes = rn.getAntecedents();
				for (final Antecedent ante : antes) {
					engine.enqueueWalker(new Expander(ante.mAntecedent));
				}
			}
		}
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
	public ProofTermGenerator(final Theory t) {
		mTheory = t;
	}
	public Theory getTheory() {
		return mTheory;
	}

	Term getTerm(final Clause cls) {
		return mNodes.get(cls);
	}

	Term getConverted() {
		return mConverted.pop();
	}

	void pushConverted(final Term res) {
		assert res.getSort().getName().equals("@Proof");
		mConverted.push(res);
	}

	void setResult(final Clause cls, final Term res) {
		mNodes.put(cls, res);
	}

	public Term convert(final Clause cls) {
		assert cls.getProof() != null;
		run(new Expander(cls));
		final Term res = mConverted.pop();
		return new FixResolutionProof().fix(res);
	}
}
