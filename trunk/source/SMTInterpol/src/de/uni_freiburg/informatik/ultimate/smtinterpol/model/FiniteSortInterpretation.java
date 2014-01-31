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

import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.IRAConstantFormatter;
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
	/**
	 * The set of all terms.
	 */
	private final HashSet<Term> mTerms = new HashSet<Term>();
	@Override
	public boolean isFinite() {
		return true;
	}

	@Override
	public void extend(Term termOfSort) {
		mTerms.add(termOfSort);
	}

	@Override
	public Term toSMTLIB(Theory t, Sort sort) {
		IRAConstantFormatter format = t.getLogic().isIRA()
				? new IRAConstantFormatter() : null;
		TermVariable var = t.createTermVariable("@v", sort);
		Term[] disj = new Term[mTerms.size()];
		int i = -1;
		for (Term term : mTerms)
			disj[++i] = t.equals(var, format == null
				? term : format.transform(term));
		return t.forall(new TermVariable[] {var}, t.or(disj));
	}

	@Override
	public Term peek() {
		if (mTerms.isEmpty())
			return null;
		return mTerms.iterator().next();
	}

	@Override
	public Term constrain(Theory t, Term input) {
		Term[] disj = new Term[mTerms.size()];
		int i = -1;
		for (Term term : mTerms)
			disj[++i] = t.equals(input, term);
		return t.or(disj);
	}

}
