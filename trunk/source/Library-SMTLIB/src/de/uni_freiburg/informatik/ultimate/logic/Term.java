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
 * This is the base class for representing SMTLIB 2 terms.
 * You can assume that every term is one of the following sub-classes:
 * <ul>
 * <li>{@link ApplicationTerm} represents a function application
 * <code>(name ...)</code>.</li>
 * <li>{@link AnnotatedTerm} represents an annotated term
 * <code>(! term ...)</code>.</li>
 * <li>{@link ConstantTerm} represents a numeral, decimal, bit vector, or string
 * literal.</li>
 * <li>{@link LetTerm} represents a let term 
 * <code>(let ((var term)...) term)</code>.</li>
 * <li>{@link TermVariable} represents a term variable <code>var</code> used in
 * quantifier or let term.
 * 	    Note that constants are represented by ApplicationTerm.</li>
 * <li>{@link QuantifiedFormula} represents a quantified formula
 * <code>(exists/forall ...)</code>.</li>
 * </ul>
 * 
 * In principle it is possible to write your own sub-classes, but that is
 * dangerous and only recommend for the advanced SMTInterpol hacker.
 * 
 * @author Juergen Christ, Jochen Hoenicke
 */
public abstract class Term {
	private final int mHash;
	
	/**
	 * A temporary counter used e.g. to count the number of occurrences of this
	 * term in a bigger term.
	 * Don't use this!!!!
	 */
	public int mTmpCtr;
	
	TermVariable[] mFreeVars;
	
	/**
	 * Create a term.
	 * @param hash the hash code of the term.  This should be stable.
	 */
	protected Term(int hash) {
		mHash = hash;
	}

	/**
	 * Returns the SMTLIB sort of this term.
	 * @return the sort of the term.
	 */
	public abstract Sort getSort();

	/**
	 * Computes and returns the free variables occurring in this term.
	 * @return the free variables.
	 */
	public TermVariable[] getFreeVars() {
		if (mFreeVars == null) {
			new NonRecursive().run(new ComputeFreeVariables(this));
		}
		return mFreeVars;
	}

	public Theory getTheory() {
		return getSort().mSymbol.mTheory;
	}

	/**
	 * Prints an SMTLIB representation of this term.  This 
	 * {@link FormulaLet introduces lets for common subexpressions} 
	 * to prevent exponential blow-up when printing
	 * a term with lots of sharing. 
	 * @return an SMTLIB representation.
	 */
	@Override
	public String toString() {
		final Term letted = new FormulaLet().let(this);
		return letted.toStringDirect();
	}
	
	/**
	 * Prints the canonical SMTLIB representation of this term.
	 * This does not eliminate common sub-expressions and can cause
	 * exponential blow-up.
	 * @return the canonical SMTLIB representation.
	 */
	public String toStringDirect() {
		final StringBuilder sb = new StringBuilder();
		new PrintTerm().append(sb, this);
		return sb.toString();
	}
	
	@Override
	public int hashCode() {
		return mHash;
	}

	/**
	 * Convert a term to a string in a stack based fashion.  This is used
	 * for internal purposes.  External users can just use toString()
	 * or toStringDirect().
	 * @param mTodo The stack where to put the strings and sub terms.
	 * @see PrintTerm
	 */
	protected abstract void toStringHelper(ArrayDeque<Object> mTodo);
}
