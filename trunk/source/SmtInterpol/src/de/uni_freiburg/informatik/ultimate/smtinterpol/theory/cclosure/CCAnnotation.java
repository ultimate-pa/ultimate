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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;

/**
 * Annotations for congruence-closure theory lemmata.
 * 
 * A theory lemma is annotated with a set of paths and literals on these path.
 * A special role plays the diseq literal, which is the only positive literal
 * in the clause.  In the negated clause this is the disequality that is in
 * conflict with the other equalities.
 * 
 * The main path (index 0) starts and ends with one side of the diseq literal.
 * Every step must either be explained by a literal from the clause 
 * (litsOnPaths != null), or by a congruence, i.e., there are two paths
 * explaining the equality of func and arg terms.  Trivial paths for equal func
 * or arg terms are omitted.
 *   
 * @author hoenicke
 *
 */
public class CCAnnotation implements IAnnotation {
	
	/**
	 * The disequality of the theory lemma.  This is the only positive atom 
	 * in the generated theory clause.  If this is null, then the first and
	 * last element in the main paths are distinct terms.
	 */
	CCEquality     mDiseq;

	/**
	 * A sequence of paths in (almost) arbitrary order.  The main path
	 * with index 0 must always exist and explain the diseq.  The other paths
	 * may explain congruences in different paths.
	 */
	CCTerm[][]     mPaths;

	/**
	 * For each path this is the sequence of literals explaining the steps in
	 * the path.  If an entry is null, this is a congruence explained by a
	 * different path.
	 */
	CCEquality[][] mLitsOnPaths;
	
    public CCAnnotation(CCEquality diseq, CCTerm[][] paths,
            CCEquality[][] litsOnPaths) {
        super();
        this.mDiseq = diseq;
        this.mPaths = paths;
        this.mLitsOnPaths = litsOnPaths;
    }

	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		sb.append(mDiseq);
		for (int p = 0; p < mPaths.length; p++) {
			sb.append("::(");
			for (int i = 0; i < mLitsOnPaths[p].length; i++) {
				sb.append('[').append(mPaths[p][i]).append(']');
				sb.append(mLitsOnPaths[p][i]);
			}
			sb.append('[').append(mPaths[p][mPaths[p].length - 1]).append("])");// NOPMD
		}
		sb.append(')');
		return sb.toString();
	}

	public CCEquality getDiseq() {
		return mDiseq;
	}

	public CCTerm[][] getPaths() {
		return mPaths;
	}

	public CCEquality[][] getLitsOnPaths() {
		return mLitsOnPaths;
	}

	@Override
	public String toSExpr(Theory smtTheory) {
		StringBuilder sb = new StringBuilder();
		sb.append('(');
		if (mDiseq != null)
			sb.append(mDiseq.negate().getSMTFormula(smtTheory));
		for (int p = 0; p < mPaths.length; p++) {
			sb.append(" :subpath (");
			String spacer = "";
			for (CCTerm t : mPaths[p]) {
				sb.append(spacer).append(t.toSMTTerm(smtTheory));
				spacer = " ";
			}
			sb.append(')');
		}
		sb.append(')');
		return sb.toString();
	}

	@Override
	public Term toTerm(Clause cls, Theory theory) {
		Term base = cls.toTerm(theory);
		Object[] subannots =
				new Object[2 * mPaths.length + (mDiseq == null ? 0 : 1)];
		int i = 0;
		if (mDiseq != null)
			subannots [i++] = mDiseq.getSMTFormula(theory);
		for (CCTerm[] subpath : mPaths) {
			Term[] subs = new Term[subpath.length];
			for (int j = 0; j < subpath.length; ++j)
				subs[j] = subpath[j].toSMTTerm(theory);
			subannots[i++] = ":subpath";
			subannots[i++] = subs;
		}
		Annotation[] annots = new Annotation[] {
			new Annotation(":CC", subannots)
		};
		return theory.term("@lemma", theory.annotatedTerm(annots, base));
	}
}
