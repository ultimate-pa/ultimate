/*
 * Copyright (C) 2014 University of Freiburg
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
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CongruencePath.SubPath;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.WeakCongruencePath.WeakSubPath;

/**
 * Annotation for array axiom instantiations.  This annotation introduces a new
 * element into our proof trees.  We call this element <pre>:weakpath</pre> and
 * use the following grammar for it:
 * <pre>
 * "(:weakpath " idx:Term path:Term* (lselect:Term rselect:Term path:Term*)?")"
 * </pre>.
 * The <code>idx</code> term specifies the index for which this path is built.
 * A weak path is correct, if and only if every step is justified by one of the
 * following conditions:</p>
 * <ul>
 * <li>an equality literal that occurs in the formula,</li>
 * <li>a congruence step, where the functions are equal and for each matching
 * arguments there is a <em>strong</em> subpath explaining the equality.</li>
 * <li>a store step, where one of the arrays is a store at an index different 
 * from <code>idx</code> into the other array.</li>
 * <li>a select step (only occurs in weakeq-ext) from <code>a</code> to 
 * <code>b</code>, where there is another (strong) sub path explaining the 
 * equality of <code>select(a, idx)</code> and <code>select(b, idx)</code>.
 * </li>
 * </ul>
 * <p>Note that the first two conditions are the usual conditions for sub path
 * correctness. </p>
 * 
 * <p>A weak path may occur in read-over-weakeq annotations that proof the 
 * equality between two selects over two arrays that are weakly equivalent.
 * For this, we require a weak path between these two arrays with idx being
 * one of the two indices. A second (strong) sub path asserts that the two
 * indices are equal (unless they are trivially equal).</p>
 * 
 * <p>A weak path may also occur in weakeq-ext annotations that proof the 
 * equality of two arrays.  In that case the first path is the main path, 
 * which may contain store steps for arbitrary indices.  For each such 
 * index there must be a weak path between the same two arrays.</p>
 *
 * @author Juergen Christ, Jochen Hoenicke
 */
public class ArrayAnnotation extends CCAnnotation {

	enum RuleKind {
		READ_OVER_WEAKEQ(":read-over-weakeq"),
		WEAKEQ_EXT(":weakeq-ext");
		
		String mKind;
		private RuleKind(String kind) {
			mKind = kind;
		}
		
		public String getKind() {
			return mKind;
		}
	}
	
	final CCTerm[] mWeakIndices;
	
	final RuleKind mRule;
	
	public ArrayAnnotation(CCEquality diseq, Collection<SubPath> paths,
			RuleKind rule) {
		super(diseq, paths);
		mWeakIndices = new CCTerm[mPaths.length];
		int i = 0;
		for (SubPath p : paths) {
			mWeakIndices[i++] = p instanceof WeakSubPath
					? ((WeakSubPath) p).getIndex() : null;
		}
		mRule = rule;
	}

	public CCTerm[] getWeakIndices() {
		return mWeakIndices;
	}
	
	@Override
	public Term toTerm(Clause cls, Theory theory) {
		Term base = cls.toTerm(theory);
		Object[] subannots =
				new Object[2 * mPaths.length + (mDiseq == null ? 0 : 1)];
		int i = 0;
		if (mDiseq != null)
			subannots [i++] = mDiseq.getSMTFormula(theory);
		for (int p = 0; p < mPaths.length; ++p) {
			CCTerm idx = mWeakIndices[p];
			CCTerm[] path = mPaths[p];

			Term[] subs = new Term[path.length];
			for (int j = 0; j < path.length; ++j)
				subs[j] = path[j].toSMTTerm(theory);
			if (idx != null) {
				subannots[i++] = ":weakpath";
				subannots[i++] = new Object[] {
					mWeakIndices[p].toSMTTerm(theory), subs
				};
			} else {
				subannots[i++] = ":subpath";
				subannots[i++] = subs;
			}
		}
		Annotation[] annots = new Annotation[] {
			new Annotation(mRule.getKind(), subannots)
		};
		return theory.term("@lemma", theory.annotatedTerm(annots, base));
	}

}
