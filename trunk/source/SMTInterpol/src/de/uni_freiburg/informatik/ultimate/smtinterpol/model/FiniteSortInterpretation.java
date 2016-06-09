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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * A finite sort interpretation.  This can be used for every uninterpreted sort
 * that does not occur under a quantifier.  Quantified formulas may axiomatize
 * homomorphisms between an uninterpreted sort and an infinite sort:
 * (forall ((i Int)(j Int)) (=> (distinct i j) (distinct (f i) (f j))))
 * @author Juergen Christ
 */
public class FiniteSortInterpretation implements SortInterpretation {
	
	private int mSize = 0;
	
	@Override
	public Term toSMTLIB(Theory t, Sort sort) {
		final TermVariable var = t.createTermVariable("@v", sort);
		final Term[] disj = new Term[mSize];
		for (int i = 0; i < mSize; ++i) {
			disj[i] = t.equals(var, genModelTerm(i, t, sort));
		}
		return t.forall(new TermVariable[] {var}, t.or(disj));
	}
	
	@Override
	public int ensureCapacity(int numValues) {
		if (mSize < numValues) {
			mSize = numValues;
		}
		return mSize;
	}

	@Override
	public int size() {
		return mSize;
	}

	@Override
	public Term get(int idx, Sort s, Theory t) throws IndexOutOfBoundsException {
		if (idx < 0 || idx >= mSize) {
			throw new IndexOutOfBoundsException();
		}
		return genModelTerm(idx, t, s);
	}

	private Term genModelTerm(int idx, Theory t, Sort s) {
		return t.term(t.getFunctionWithResult("@" + idx, null, s));
	}

	@Override
	public int extendFresh() {
		return mSize++;
	}

}
