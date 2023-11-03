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
 * Represents a lambda term SMTLIB 3. This class represents the SMTLIB 3
 * construct
 *
 * <pre>
 * (lambda ((var_1 sort_1) ... (var_n sort_n)) term)
 * </pre>
 *
 * @author hoenicke
 */
public class LambdaTerm extends Term {
	private final TermVariable[] mVariables;
	private final Term mSubTerm;
	private final Sort mSort;

	LambdaTerm(final TermVariable[] vars, final Term subterm, final int hash) {
		super(hash);
		mVariables = vars;
		mSubTerm = subterm;
		Sort mySort = subterm.getSort();
		for (int i = vars.length - 1; i >= 0; i--) {
			mySort = mySort.getTheory().getSort(SMTLIBConstants.FUNC, vars[i].getSort(), mySort);
		}
		mSort = mySort;
	}

	/**
	 * Get the quantified variables.
	 * @return the variables
	 */
	public TermVariable[] getVariables() {
		return mVariables;
	}

	/**
	 * Get the formula under the quantifier.
	 * @return the sub-formula.
	 */
	public Term getSubterm() {
		return mSubTerm;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	public static final int hashLambda(final TermVariable[] vars, final Term f) {
		return HashUtils.hashJenkins(f.hashCode(), (Object[]) vars);
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> mTodo) {
		// Add subterm to stack.
		mTodo.addLast(")");
		mTodo.addLast(getSubterm());
		mTodo.addLast(")) ");

		// Add variables
		final TermVariable[] vars = getVariables();
		for (int i = vars.length - 1; i > 0; i--) {
			mTodo.addLast(vars[i].getSort());
			mTodo.addLast(") (" + vars[i] + " ");
		}
		mTodo.addLast(vars[0].getSort());

		// Print out the quantifier.
		mTodo.addLast("(lambda ((" + vars[0] + " ");
	}
}
