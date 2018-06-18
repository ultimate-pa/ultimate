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

import java.math.BigInteger;

/**
 * Represents a function symbol.  Each function symbol has a name, a sort and
 * zero or more parameter sorts.  A constant symbol is represented as a function
 * symbols with zero parameters.
 * 
 * For parametric functions we create a different FunctionSymbol for every 
 * instantiation.
 * 
 * @author hoenicke
 */
public class FunctionSymbol {
	public static final int INTERNAL   = 1;
	public static final int LEFTASSOC  = (1) << 1;
	public static final int RIGHTASSOC = (2) << 1;
	public static final int CHAINABLE  = (3) << 1;// NOCHECKSTYLE
	public static final int PAIRWISE   = (4) << 1;// NOCHECKSTYLE
	public static final int ASSOCMASK  = (7) << 1;// NOCHECKSTYLE
	
	public static final int RETURNOVERLOAD = 16;
	public static final int MODELVALUE = 32;

	final String mName;
	final BigInteger[] mIndices;
	final Sort[] mParamSort;
	final Sort mReturnSort;
	final int mFlags;
	final TermVariable[] mDefinitionVars;
	final Term mDefinition;
	
	FunctionSymbol(String n, BigInteger[] i, Sort[] params, Sort result,
			TermVariable[] definitionVars, Term definition, int flags) {
		mName = n;
		mIndices = i;
		mParamSort = params;
		mReturnSort = result;
		mFlags = flags;
		mDefinition = definition;
		mDefinitionVars = definitionVars;
		if (isLeftAssoc() 
				&& (params.length != 2 || !params[0].equalsSort(result))) {
			throw new IllegalArgumentException(
					"Wrong sorts for left-associative symbol");
		}
		if (isRightAssoc() 
				&& (params.length != 2 || !params[1].equalsSort(result))) {
			throw new IllegalArgumentException(
					"Wrong sorts for right-associative symbol");
		}
		if ((isChainable() || isPairwise())
				&& (params.length != 2 || !params[0].equalsSort(params[1])
                   	|| !result.equalsSort(getTheory().getBooleanSort()))) {
			throw new IllegalArgumentException(
					"Wrong sorts for chainable symbol");
		}
	}
	
	@Override
	public int hashCode() {
		return mName.hashCode();
	}
	
	/**
	 * Get the name of the function. This is the name as used in an SMTLIB
	 * script.  It can also contain symbols not allowed by the SMTLIB standard.
	 * In that case the string representation uses <code>|</code> to quote
	 * the name.  The name may not contain <code>|</code> symbols. 
	 * @return the name of the function.
	 */
	public String getName() {
		return mName;
	}
	
	public BigInteger[] getIndices() {
		return mIndices;
	}
	/**
	 * Check whether this function symbol is created by the solver.  Symbols
	 * created by the solver are assumed to be special symbols like
	 * <code>+</code>, <code>-</code>, or internal symbols only used by the
	 * solver. 
	 * @return true if and only if the function symbol was flagged as internal.
	 */
	public boolean isIntern() {
		return (mFlags & INTERNAL) != 0;
	}
	
	public boolean isModelValue() {
		return (mFlags & MODELVALUE) != 0;
	}
	
	public Theory getTheory() {
		return mReturnSort.mSymbol.mTheory;
	}
	
	/**
	 * @deprecated use getParameterSorts().length
	 * @return the number of parameters this function takes.
	 */
	@Deprecated
	public int getParameterCount() {
		return mParamSort.length;
	}
	
	/**
	 * @deprecated use getParameterSorts()[i].
	 * @param i the parameter number.
	 * @return the sort of the ith parameter.
	 */
	@Deprecated
	public Sort getParameterSort(int i) {
		return mParamSort[i];
	}
	/**
	 * Retrieve the variables used in the definition of this function symbol.
	 * A definition only exists if the function symbol is a macro created by the
	 * {@link Script#defineFun(String, TermVariable[], Sort, Term) define-fun}
	 * command or a <code>:named</code> annotation.
	 * @return The variables used in the definition of this function symbol or 
	 *         <code>null</code> if this function symbol is not a macro.
	 */
	public TermVariable[] getDefinitionVars() {
		return mDefinitionVars;
	}
	/**
	 * Retrieve the definition of this function symbol.  A definition only
	 * exists if the function symbol is a macro created by the 
	 * {@link Script#defineFun(String, TermVariable[], Sort, Term) define-fun}
	 * command or a <code>:named</code> annotation.
	 * @return The definition of this function symbol or <code>null</code> if
	 *         this function symbol is not a macro.
	 */
	public Term getDefinition() {
		return mDefinition;
	}
	
	/**
	 * Get the return sort of this function.
	 * @return the return sort.
	 */
	public Sort getReturnSort() {
		return mReturnSort;
	}
	
	/**
	 * Get the sort of the parameters for this function.
	 * @return An array with the parameter sorts.  Never write to this array!
	 */
	public Sort[] getParameterSorts() {
		return mParamSort;
	}
	
	private final void checkSort(Term arg, Sort sort) {
		final Sort argSort = arg.getSort();
		if (!sort.equalsSort(argSort)) {
			if (argSort.toString().equals(sort.toString())) {
				throw new SMTLIBException(
						"Argument " + arg + " comes from wrong theory.");
			} else {
				throw new SMTLIBException(
						"Argument " + arg + " has type " + argSort
						+ " but function " + mName + " expects " + sort);
			}
		}
	}
	
	/**
	 * Check if this function symbol can be called on the given argument terms.
	 * This throws an exception if the type check fails.
	 * @param params the arguments for the function symbols.
	 */
	public void typecheck(Term[] params) throws SMTLIBException {
		assert params.getClass() == Term[].class;
		if ((mFlags & (ASSOCMASK)) != 0) { // NOPMD
			// All arguments should have the same type.
			if (params.length < 2) {
				throw new SMTLIBException(
					"Function " + mName + " expects at least two arguments.");
			}
			checkSort(params[0], mParamSort[0]);
			checkSort(params[params.length - 1], mParamSort[1]);
			final Sort otherSort = isLeftAssoc() ? mParamSort[1] : mParamSort[0];
			for (int i = 1; i < params.length - 1; i++) {
				checkSort(params[i], otherSort);
			}
		} else {
			if (params.length != mParamSort.length) {
				throw new SMTLIBException(
					"Function " + mName + " expects " + mParamSort.length
						+ " arguments.");
			}
			for (int i = 0; i < mParamSort.length; i++) {
				checkSort(params[i], mParamSort[i]);
			}
		}
	}
	
	/**
	 * Check if this function symbol can be called on terms with the given sort.
	 * @param params the sort of the arguments for the function symbols.
	 * @return true if the type check succeeds, false otherwise.
	 */
	public boolean typecheck(Sort[] params) {
		if ((mFlags & (ASSOCMASK)) != 0) { // NOPMD
			assert (mParamSort.length == 2);
			if (params.length < 2) {
				return false;
			}
			if (!params[0].equalsSort(mParamSort[0])) {
				return false;
			}
			if (!params[params.length - 1].equalsSort(mParamSort[1])) {
				return false;
			}
			final Sort otherSort = isLeftAssoc() ? mParamSort[1] : mParamSort[0];
			for (int i = 1; i < params.length - 1; i++) {
				if (!params[i].equalsSort(otherSort)) {
					return false;
				}
			}
		} else {
			if (params.length != mParamSort.length) {
				return false;
			}
			for (int i = 0; i < mParamSort.length; i++) {
				if (!params[i].equalsSort(mParamSort[i])) {
					return false;
				}
			}
		}
		return true;
	}
	
	/**
	 * Returns a string representation of this object.  This is a SMTLIB
	 * like representation of the following form:
	 * <pre>(name paramsort1 ... paramsortn returnsort)</pre>
	 * where name is the (possibly indexed and quoted) function name.
	 */
	@Override
	public String toString() {
		final StringBuffer sb = new StringBuffer();
		final String name = PrintTerm.quoteIdentifier(mName);
		sb.append('(');
		if (mIndices == null) {
			sb.append(name);
		} else {
			sb.append("(_ ").append(name);
			for (final BigInteger i : mIndices) {
				sb.append(' ').append(i);
			}
			sb.append(')');
		}
		for (final Sort s : mParamSort) {
			sb.append(' ').append(s);
		}
		sb.append(' ').append(mReturnSort);
		sb.append(')');
		return sb.toString();
	}

	/**
	 * Checks if this function symbol was declared as chainable.
	 * This should only be true for the internal equality function.
	 * @return true if the function symbol is chainable.
	 */
	public final boolean isChainable() {
		return (mFlags & ASSOCMASK) == CHAINABLE;
	}
	/**
	 * Checks if this function symbol was declared as pairwise.
	 * This should only be true for the internal distinct function.
	 * @return true if the function symbol is pairwise.
	 */
	public final boolean isPairwise() {
		return (mFlags & ASSOCMASK) == PAIRWISE;
	}
	/**
	 * Checks if this function symbol was declared as left associative.
	 * This should only be true for internal function symbols.
	 * @return true if the function symbol is left associative.
	 */
	public final boolean isLeftAssoc() {
		return (mFlags & ASSOCMASK) == LEFTASSOC;
	}
	/**
	 * Checks if this function symbol was declared as right associative.
	 * This should only be true for internal function symbols.
	 * @return true if the function symbol is right associative.
	 */
	public final boolean isRightAssoc() {
		return (mFlags & ASSOCMASK) == RIGHTASSOC;
	}
	
	/**
	 * Checks if this function symbol was created with the SMTLIB
	 * syntax <code>(as name sort)</code> to give it a different result 
	 * sort.
	 * @return true if the sort was explicitly given, false if it is implicit.
	 */
	public final boolean isReturnOverload() {
		return (mFlags & RETURNOVERLOAD) != 0;
	}

	/**
	 * Get the string representation of this function symbol as it would
	 * be used to build an application term.
	 * @return the string representation.
	 */
	public String getApplicationString() {
		final String name = PrintTerm.quoteIdentifier(mName);
		if (mIndices == null && !isReturnOverload()) {
			return name;
		}
		final StringBuffer sb = new StringBuffer();
		if (isReturnOverload()) {
			sb.append("(as ");
		}
		if (mIndices != null) {
			sb.append("(_ ");
		}
		sb.append(name);
		if (mIndices != null) {
			for (final BigInteger i : mIndices) {
				sb.append(' ').append(i);
			}
			sb.append(')');
		}
		if (isReturnOverload()) {
			sb.append(' ').append(getReturnSort()).append(')');
		}
		return sb.toString();
	}
	/**
	 * Check whether this function symbol is an internal symbol that has a fixed
	 * semantic.
	 * @return true if and only if the symbol is an internal symbol with a fixed
	 *         semantic.
	 */
	public boolean isInterpreted() {
		return isModelValue()
				|| (isIntern() && (mName.charAt(0) != '@' || !mName.endsWith("0")));
	}
}
