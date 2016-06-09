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
	
	private final int mQuantifier;
	private final TermVariable[] mVariables;
	private final Term mSubFormula;
	
	QuantifiedFormula(int quant, TermVariable[] vars, Term f, int hash) {
		super(hash);
		mQuantifier = quant;
		mVariables = vars;
		mSubFormula = f;
	}
	
	/**
	 * @return the quantifier
	 */
	public int getQuantifier() {
		return mQuantifier;
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
	public Term getSubformula() {
		return mSubFormula;
	}

	@Override
	public Sort getSort() {
		return mSubFormula.getSort();
	}

	@Override
	public int hashCode() {
		return hashQuantifier(mQuantifier, mVariables, mSubFormula);
	}
	
	public static final int hashQuantifier(
			int quant, TermVariable[] vars, Term f) {
		return //Arrays.hashCode(vars) ^ f.hashCode() ^ quant;
			HashUtils.hashJenkins(f.hashCode() ^ quant, (Object[]) vars);
	}

	@Override
	public void toStringHelper(ArrayDeque<Object> mTodo) {
		// Add subterm to stack.
		mTodo.addLast(")");
		mTodo.addLast(getSubformula());
		mTodo.addLast(")) ");
		
		// Add variables
		final TermVariable[] vars = getVariables();
		for (int i = vars.length - 1; i > 0; i--) {
			mTodo.addLast(vars[i].getSort());
			mTodo.addLast(") (" + vars[i] + " ");
		}
		mTodo.addLast(vars[0].getSort());

		// Print out the quantifier.
		mTodo.addLast("(" + (getQuantifier() == EXISTS ? "exists" : "forall")
				+ " ((" + vars[0] + " ");
	}
}
