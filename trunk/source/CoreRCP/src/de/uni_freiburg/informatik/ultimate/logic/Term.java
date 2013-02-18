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

public abstract class Term {	
	protected int m_Hash;
	
	/**
	 * A temporary counter used e.g. to count the number of occurrences of this
	 * term in a bigger term.
	 */
	public int tmpCtr;
	
	TermVariable[] m_freeVars;
	
	protected Term(int hash) {
		m_Hash = hash;
	}

	public abstract Sort getSort();

	public TermVariable[] getFreeVars() {
		if (m_freeVars == null)
			new NonRecursive().run(new ComputeFreeVariables(this));
		return m_freeVars;
	}

	public Theory getTheory() {
		return getSort().m_Symbol.m_Theory;
	}
	
	public String toString() {
		Term letted = (new FormulaLet()).let(this);
		return letted.toStringDirect();
	}
	
	public String toStringDirect() {
		StringBuilder sb = new StringBuilder();
		new PrintTerm().append(sb, this);
		return sb.toString();
	}
	
	public int hashCode() {
		return m_Hash;
	}

	/**
	 * Convert a term to a string in a stack based fashion.  This is used
	 * for internal purposes.  External users can just use toString()
	 * or toStringDirect().
	 * @param m_Todo The stack where to put the strings and sub terms.
	 * @see PrintTerm
	 */
	public abstract void toStringHelper(ArrayDeque<Object> m_Todo);
}