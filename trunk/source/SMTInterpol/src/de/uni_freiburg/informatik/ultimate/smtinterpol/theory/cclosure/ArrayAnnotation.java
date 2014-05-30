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

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.dpll.Clause;

/**
 * Annotation for array axiom instantiations.  This annotation introduces a new
 * element into our proof trees.  We call this element <pre>:weakpath</pre> and
 * use the following grammar for it:
 * <pre>
 * "(:weakpath " idx:Term path:Term* (lselect:Term rselect:Term path:Term*)?")"
 * </pre>.
 * The <pre>idx</pre> term specifies the index for which this path is built.
 * If the path contains a weak modulo i step, we have a sub path that contains
 * the left and right end of the weak modulo i step in <pre>lselect</pre> resp.
 * <pre>rselect</pre>.  In this case, we require additional paths justifying the
 * equivalence of <pre>lselect</pre> and <pre>rselect</pre>.  Furthermore, if
 * the index of <pre>lselect</pre> resp. <pre>rselect</pre> differ from
 * <pre>idx</pre>, we require a path justifying the equivalence of
 * <pre>idx</pre> and the corresponding index.
 * 
 * A weak path is correct, if and only if every step is justified by one of the
 * following conditions:
 * <ul>
 * <li>an equivalence between two arrays (a=b),</li>
 * <li>a congruence between two stores that is justified by a congruence path
 * (annotation <pre>:subpath</pre>),</li>
 * <li>one of the arrays is a store at an index different from <pre>idx</pre>
 * into the other array,</li>
 * <li>a subpath ends at an array that is the array for the select of the next
 * weak modulo i step and the index of this select is congruent to
 * <pre>idx</pre> as justified by a <pre>:subpath</pre>,</li>
 * <li>the right hand side of a weak modulo i step selects on an array that is
 * the start of the next sub path and the index of the select is congruent to
 * <pre>idx</pre> as justified by a <pre>:subpath</pre>, or</li>
 * <li>the step is a weak modulo i step in which case there needs to be a
 * <pre>:subpath</pre> justifying the equivalence of the selects.</li>
 * </ul>
 * Note that in the last condition we do not explicitly require a path stating
 * equivalence of the indices.  Such a path might be present, but is not needed
 * since we already require the presence of paths justifying the equivalence
 * between the select indices and the path index.
 * @author Juergen Christ
 */
public class ArrayAnnotation extends CCAnnotation {

	enum RuleKind {
		READ_OVER_WEAKEQ {
			public String toString() {
				return ":read-over-weakeq";
			}
		},
		WEAKEQ_EXT {
			public String toString() {
				return ":weakeq-ext";
			}
		}
	}
	
	final CCTerm[] mWeakIndices;
	final CCTerm[][] mWeakPaths;
	
	final RuleKind mRule;
	
	public ArrayAnnotation(CCEquality diseq, CCTerm[][] paths,
			CCEquality[][] litsOnPaths,
			CCTerm[] weakIndices, CCTerm[][] weakPaths, RuleKind rule) {
		super(diseq, paths, litsOnPaths);
		mWeakIndices = weakIndices;
		mWeakPaths = weakPaths;
		mRule = rule;
	}

	public CCTerm[] getWeakIndices() {
		return mWeakIndices;
	}
	
	public CCTerm[][] getWeakPaths() {
		return mWeakPaths;
	}
	
	@Override
	public String toSExpr(Theory smtTheory) {
		// TODO This function should be removed!!!
		return null;
	}

	@Override
	public Term toTerm(Clause cls, Theory theory) {
		Term base = cls.toTerm(theory);
		Object[] subannots =
				new Object[2 * mPaths.length + 2 * mWeakPaths.length
				           + (mDiseq == null ? 0 : 1)];
		int i = 0;
		if (mDiseq != null)
			subannots [i++] = mDiseq.getSMTFormula(theory);
		for (int p = 0; p < mWeakPaths.length; ++p) {
			CCTerm[] weakpath = mWeakPaths[p];
			Term[] subs = new Term[weakpath.length];
			for (int j = 0; j < weakpath.length; ++j)
				subs[j] = weakpath[j].toSMTTerm(theory);
			subannots[i++] = ":weakpath";
			subannots[i++] = new Object[] {
				mWeakIndices[p].toSMTTerm(theory), subs
			};
		}
		for (CCTerm[] subpath : mPaths) {
			Term[] subs = new Term[subpath.length];
			for (int j = 0; j < subpath.length; ++j)
				subs[j] = subpath[j].toSMTTerm(theory);
			subannots[i++] = ":subpath";
			subannots[i++] = subs;
		}
		Annotation[] annots = new Annotation[] {
			// TODO: Should we mention :ARRAY somehow???
			new Annotation(mRule.toString(), subannots)
		};
		return theory.term("@lemma", theory.annotatedTerm(annots, base));
	}

}
