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

import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
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
	private final Model mModel;
	private final ArrayList<Term> mValues;

	public FiniteSortInterpretation(Model model) {
		mModel = model;
		mValues = new ArrayList<>();
	}

	@Override
	public Term toSMTLIB(final Theory t, final Sort sort) {
		final TermVariable var = t.createTermVariable("@v", sort);
		final Term[] disj = new Term[mValues.size()];
		for (int i = 0; i < mValues.size(); i++) {
			disj[i] = t.equals(var, mValues.get(i));
		}
		return t.forall(new TermVariable[] {var}, t.or(disj));
	}

	@Override
	public void register(Term term) {
		assert ((ApplicationTerm) term).getFunction().isModelValue();
	}

	@Override
	public Term extendFresh(final Sort sort) {
		final Theory theory = sort.getTheory();
		final int idx = mModel.getFreshModelValue();
		final Term value = theory.term(theory.getFunctionWithResult("@" + idx, null, sort));
		mValues.add(value);
		return value;
	}

	@Override
	public Term getModelValue(final int idx, final Sort sort) {
		while (idx >= mValues.size()) {
			extendFresh(sort);
		}
		return mValues.get(idx);
	}
}
