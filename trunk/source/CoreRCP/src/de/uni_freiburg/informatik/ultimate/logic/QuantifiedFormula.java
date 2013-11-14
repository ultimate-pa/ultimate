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
 * Represents a quantified formula in SMTLIB 2.  This class represents the
 * SMTLIB 2 construct
 * <pre>
 * (forall ((var_1 sort_1) ... (var_n sort_n)) ...)
 * </pre> or
 * <pre>
 * (exists ((var_1 sort_1) ... (var_n sort_n)) ...)
 * </pre>.
 *
 * A quantified formula is created by 
 * {@link Script#quantifier(int, TermVariable[], Term, Term[][])}.
 *
 * @author hoenicke
 */
public class QuantifiedFormula extends Term {
	public static final int EXISTS = 0;
	public static final int FORALL = 1;
	
	private int m_Quantifier;
	private TermVariable[] m_Variables;
	private Term m_SubFormula;
	
	QuantifiedFormula(int quant, TermVariable[] vars, Term f, int hash) {
		super(hash);
		this.m_Quantifier = quant;
		this.m_Variables = vars;
		this.m_SubFormula = f;
	}
	
	/**
	 * @return the quantifier
	 */
	public int getQuantifier() {
		return m_Quantifier;
	}

	/**
	 * Get the quantified variables.  
	 * @return the variables
	 */
	public TermVariable[] getVariables() {
		return m_Variables;
	}

	/**
	 * Get the formula under the quantifier.
	 * @return the sub-formula.
	 */
	public Term getSubformula() {
		return m_SubFormula;
	}

	@Override
	public Sort getSort() {
		return m_SubFormula.getSort();
	}

	public int hashCode() {
		return hashQuantifier(m_Quantifier, m_Variables, m_SubFormula);
	}
	
	public static final int hashQuantifier(
			int quant, TermVariable[] vars, Term f) {
		return //Arrays.hashCode(vars) ^ f.hashCode() ^ quant;
			HashUtils.hashJenkins(f.hashCode() ^ quant, (Object[]) vars);
	}

	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		// Add subterm to stack.
		m_Todo.addLast(")");
		m_Todo.addLast(getSubformula());
		m_Todo.addLast(")) ");
		
		// Add variables
		TermVariable[] vars = getVariables();
		for (int i = vars.length-1; i > 0; i--) {
			m_Todo.addLast(vars[i].getSort());
			m_Todo.addLast(") ("+vars[i]+" ");
		}
		m_Todo.addLast(vars[0].getSort());

		// Print out the quantifier.
		m_Todo.addLast("(" + (getQuantifier() == EXISTS ? "exists" : "forall")
				+ " ((" + vars[0] + " ");
	}
}
