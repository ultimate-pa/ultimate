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

/**
 * Represents a term variable that is used in a {@link LetTerm lets}, 
 * {@link QuantifiedFormula quantified formulas}, and
 * {@link Script#defineFun(String, TermVariable[], Sort, Term) define-fun}.
 * 
 * Term variables are created by {@link Script#variable(String, Sort)}.
 * 
 * @author Juergen Christ
 */
public class TermVariable extends Term {
	private final String mName;
	private final Sort mSort;
	
	TermVariable(String n, Sort s, int hash) {
		super(hash);
		mName = n;
		mSort = s;
	}
	
	/**
	 * Return the name of the variable.
	 * @return the name of the variable.
	 */
	public String getName() {
		return mName;
	}

	/**
	 * Return the declared sort of the variable.
	 * @return the sort of the variable that was used to declare the variable.
	 * This is not expanded if the sort is a defined sort.
	 */
	public Sort getDeclaredSort() {
		return mSort;
	}
	
	/**
	 * Return the (expanded) sort of the variable.
	 * @return the expanded sort of the variable.
	 */
	@Override
	public Sort getSort() {
		return mSort.getRealSort();
	}
	
	/**
	 * The SMTLIB representation of the term.
	 */
	@Override
	public String toString() {
		return PrintTerm.quoteIdentifier(mName);
	}

	static final int hashVariable(String name, Sort sort) {
		return name.hashCode() ^ sort.hashCode();
	}

	/**
	 * {@inheritDoc}
	 */
	@Override
	public void toStringHelper(ArrayDeque<Object> mTodo) {
		mTodo.add(toString());
	}
}
