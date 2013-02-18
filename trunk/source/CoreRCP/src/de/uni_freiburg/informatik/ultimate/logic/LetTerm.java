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

public class LetTerm extends Term {
	private TermVariable[] m_Variables;
	private Term[] m_Values;
	private Term m_Subterm;
	
	/**
	 * @return the variable
	 */
	public TermVariable[] getVariables() {
		return m_Variables;
	}

	/**
	 * @return the value
	 */
	public Term[] getValues() {
		return m_Values;
	}

	/**
	 * @return the subformula
	 */
	public Term getSubTerm() {
		return m_Subterm;
	}

	LetTerm(TermVariable[] vars, Term[] vals, Term t, int hash) {
		super(hash);
		this.m_Variables = vars;
		this.m_Values = vals;
		this.m_Subterm = t;
	}
	
	@Override
	public Sort getSort() {
		LetTerm sortterm = this;
		while (sortterm.m_Subterm instanceof LetTerm)
			sortterm = (LetTerm) sortterm.m_Subterm;
		return sortterm.m_Subterm.getSort();
	}

	public static final int hashLet(
			TermVariable[] vars, Term[] values, Term subform) {
//		return Arrays.hashCode(vars) ^ Arrays.hashCode(values) ^ 
//			subform.hashCode();
		return HashUtils.hashJenkins(
				HashUtils.hashJenkins(subform.hashCode(), (Object[]) values),
					(Object[]) vars);
	}
	
	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		// Add subterm to stack.
		m_Todo.addLast(")");
		m_Todo.addLast(getSubTerm());
		m_Todo.addLast(")) ");
		// Add assigned values to stack
		TermVariable[] vars = getVariables();
		Term[] values = getValues();
		for (int i = values.length-1; i > 0; i--) {
			m_Todo.addLast(values[i]);
			m_Todo.addLast(") ("+vars[i].toString()+" ");
		}	
		m_Todo.addLast(values[0]);
		m_Todo.addLast("(let (("+vars[0].toString()+" ");
	}
}
