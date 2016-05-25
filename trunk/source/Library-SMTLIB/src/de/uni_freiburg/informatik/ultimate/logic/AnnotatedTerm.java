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
package de.uni_freiburg.informatik.ultimate.logic;

import java.util.ArrayDeque;
//import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Representation of annotated terms in SMTLIB 2.  This class stores terms of
 * the form
 * <pre>
 * (! ... :key_1 value_1 ... :key_n value_n)
 * </pre>
 *
 * An annotated term is created by 
 * {@link Script#annotate(Term, Annotation...)}.
 *
 * @author hoenicke
 */
public class AnnotatedTerm extends Term {
	private final Term mSubterm;
	private final Annotation[] mAnnotations;
	
	AnnotatedTerm(Annotation[] annots, Term term, int hash) {
		super(hash);
		mAnnotations = annots;
		mSubterm = term;
	}
	
	@Override
	public Sort getSort() {
		return mSubterm.getSort();
	}
	/**
	 * Get the term that is annotated by the annotations stored in this term.
	 * @return The subterm of this term.
	 */
	public Term getSubterm() {
		return mSubterm;
	}
	/**
	 * Get all annotations stored in this term.  The resulting array should not
	 * be modified!
	 * @return The annotations stored in this term.
	 */
	public Annotation[] getAnnotations() {
		return mAnnotations;
	}
	
	public static int hashAnnotations(Annotation[] annots, Term subTerm) {
		return //subTerm.hashCode() * 31 + Arrays.hashCode(annots);
			HashUtils.hashJenkins(subTerm.hashCode(), (Object[])annots);
	}
	
	@Override
	public void toStringHelper(ArrayDeque<Object> mTodo) {
		// Add annotations to stack.
		mTodo.addLast(")");
		final Annotation[] annots = getAnnotations();
		for (int i = annots.length - 1; i >= 0; i--) {
			if (annots[i].getValue() != null) {
				mTodo.addLast(annots[i].getValue());
				mTodo.addLast(" ");
			}
			mTodo.addLast(" " + annots[i].getKey());
		}
		mTodo.addLast(getSubterm());
		mTodo.addLast("(! ");
	}
}
