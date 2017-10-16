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

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.IAnnotation;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CongruencePath.SubPath;

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
	 * A sequence of paths.  The main path with index 0 must always exist
	 * and explain the diseq.  The other paths must be in such an order
	 * that later paths explain congruences on earlier.
	 */
	CCTerm[][]     mPaths;

	public CCAnnotation(final CCEquality diseq, final Collection<SubPath> paths) {
		super();
		mDiseq = diseq;
		mPaths = new CCTerm[paths.size()][];
		int i = 0;
		for (final SubPath p : paths) {
			mPaths[i++] = p.getTerms();
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append('(');
		sb.append(mDiseq);
		for (int p = 0; p < mPaths.length; p++) {
			sb.append("::(");
			String comma = "";
			for (final CCTerm term : mPaths[p]) {
				sb.append(comma).append(term);
				comma = " ";
			}
			sb.append(')');
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

	@Override
	public Term toTerm(final Clause cls, final Theory theory) {
		final Term base = cls.toTerm(theory);
		final Object[] subannots =
				new Object[2 * mPaths.length + (mDiseq == null ? 0 : 1)];
		int i = 0;
		if (mDiseq != null) {
			subannots [i++] = mDiseq.getSMTFormula(theory);
		}
		for (final CCTerm[] subpath : mPaths) {
			final Term[] subs = new Term[subpath.length];
			for (int j = 0; j < subpath.length; ++j) {
				subs[j] = subpath[j].toSMTTerm(theory);
			}
			subannots[i++] = ":subpath";
			subannots[i++] = subs;
		}
		final Annotation[] annots = new Annotation[] {
			new Annotation(":CC", subannots)
		};
		return theory.term("@lemma", theory.annotatedTerm(annots, base));
	}
}
