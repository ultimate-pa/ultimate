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
	public static final int CHAINABLE  = (3) << 1;
	public static final int PAIRWISE   = (4) << 1;
	public static final int ASSOCMASK  = (7) << 1;

	public static final int RETURNOVERLOAD = 16;

	final String m_Name;
	final BigInteger[] m_Indices;
	final Sort[] m_ParamSort;
	final Sort m_ReturnSort;
	final int m_Flags;
	final TermVariable[] m_DefinitionVars;
	final Term m_Definition;
	
	FunctionSymbol(String n, BigInteger[] i, Sort[] params, Sort result, TermVariable[] definitionVars,
			       Term definition,
			       int flags) {
		m_Name = n;
		m_Indices = i;
		m_ParamSort = params;
		m_ReturnSort = result;
		this.m_Flags = flags;
		this.m_Definition = definition;
		this.m_DefinitionVars = definitionVars;
		if (isLeftAssoc() && 
				(params.length != 2 || !params[0].equalsSort(result)))
			throw new IllegalArgumentException
				("Wrong sorts for left-associative symbol");
		if (isRightAssoc() && 
				(params.length != 2 || !params[1].equalsSort(result)))
			throw new IllegalArgumentException
				("Wrong sorts for right-associative symbol");
		if ((isChainable() || isPairwise()) && 
				(params.length != 2 || !params[0].equalsSort(params[1]) ||
                   	!result.equalsSort(getTheory().getBooleanSort())))
			throw new IllegalArgumentException
				("Wrong sorts for chainable symbol");
	}
	
	public int hashCode() {
		return m_Name.hashCode();
	}
	
	/**
	 * Get the name of the function. This is the name as used in an SMTLIB
	 * script.  It can also contain symbols not allowed by the SMTLIB standard.
	 * In that case the string representation uses <code>|</code> to quote
	 * the name.  The name may not contain <code>|</code> symbols. 
	 * @return the name of the function.
	 */
	public String getName() {
		return m_Name;
	}
	
	public BigInteger[] getIndices() {
		return m_Indices;
	}
	/**
	 * Check whether this function symbol is created by the solver.  Symbols
	 * created by the solver are assumed to be special symbols like
	 * <code>+</code>, <code>-</code>, or internal symbols only used by the
	 * solver. 
	 * @return true if and only if the function symbol was flagged as internal.
	 */
	public boolean isIntern() {
		return (m_Flags & INTERNAL) != 0;
	}
	
	public Theory getTheory() {
		return m_ReturnSort.m_Symbol.m_Theory;
	}
	
	/**
	 * @deprecated use getParamterSorts().length 
	 */
	public int getParameterCount() {
		return m_ParamSort.length;
	}
	
	/**
	 * @deprecated use getParamterSorts()[i] 
	 */
	public Sort getParameterSort(int i) {
		return m_ParamSort[i];
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
		return m_DefinitionVars;
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
		return m_Definition;
	}
	
	/**
	 * Get the return sort of this function.
	 * @return the return sort.
	 */
	public Sort getReturnSort() {
		return m_ReturnSort;
	}
	
	/**
	 * Get the sort of the parameters for this function.
	 * @return An array with the parameter sorts.  Never write to this array!
	 */
	public Sort[] getParameterSorts() {
		return m_ParamSort;
	}
	
	private final void checkSort(Term arg, Sort sort, boolean mixRealInt)
		throws SMTLIBException
	{
		Sort argSort = arg.getSort();
		if (!sort.equalsSort(argSort)) {
			if (argSort.toString().equals(sort.toString()))
				throw new SMTLIBException
					("Argument "+arg+" comes from wrong theory.");
			else if (!mixRealInt || !argSort.getName().equals("Int"))
				throw new SMTLIBException
					("Argument "+arg+" has type "+argSort+
					 " but function "+m_Name+" expects "+sort);
		}
	}
	
	/**
	 * Check if this function symbol can be called on the given argument terms.
	 * This throws an exception if the type check fails.
	 * @param params the arguments for the function symbols.
	 */
	public void typecheck(Term[] params) throws SMTLIBException
	{
		boolean mixRealInt = false;
		if (getTheory().getLogic() != null && getTheory().getLogic().isIRA()
			&& m_ParamSort.length == 2
			&& m_ParamSort[0] == m_ParamSort[1]
			&& m_ParamSort[0] == getTheory().getSort("Real"))
			mixRealInt = true;
		if ((m_Flags & (ASSOCMASK)) != 0) {
			// All arguments should have the same type.
			if (params.length < 2)
				throw new SMTLIBException
					("Function "+m_Name+" expects at least two arguments.");
			checkSort(params[0], m_ParamSort[0], mixRealInt);
			checkSort(params[params.length-1], m_ParamSort[1], mixRealInt);
			Sort otherSort = isLeftAssoc() ? m_ParamSort[1] : m_ParamSort[0];
			for (int i = 1; i < params.length - 1; i++) {
				checkSort(params[i], otherSort, mixRealInt);
			}
		} else {
			if (params.length != m_ParamSort.length)
				throw new SMTLIBException
					("Function "+m_Name+" expects "+m_ParamSort.length+" arguments.");
			for (int i = 0; i < m_ParamSort.length; i++) {
				checkSort(params[i], m_ParamSort[i], mixRealInt);
			}
		}
	}
	
	/**
	 * Check if this function symbol can be called on terms with the given sort.
	 * @param params the sort of the arguments for the function symbols.
	 * @return true if the type check succeeds, false otherwise.
	 */
	public boolean typecheck(Sort[] params) {
		boolean mixRealInt = false;
		if (getTheory().getLogic().isIRA()
			&& m_ParamSort.length == 2
			&& m_ParamSort[0] == m_ParamSort[1]
			&& m_ParamSort[0].getName().equals("Real"))
			mixRealInt = true;
		if ((m_Flags & (ASSOCMASK)) != 0) {
			assert (m_ParamSort.length == 2);
			if (params.length < 2)
				return false;
			if (!params[0].equalsSort(m_ParamSort[0])
				&& (!mixRealInt || params[0] != getTheory().getSort("Int")))
				return false;
			if (!params[params.length-1].equalsSort(m_ParamSort[1])
				&& (!mixRealInt || params[params.length-1] != getTheory().getSort("Int")))
				return false;
			Sort otherSort = isLeftAssoc() ? m_ParamSort[1] : m_ParamSort[0];
			for (int i = 1; i < params.length - 1; i++) {
				if (!params[i].equalsSort(otherSort)
					&& (!mixRealInt || params[i] != getTheory().getSort("Int")))
					return false;
			}
		} else {
			if (params.length != m_ParamSort.length)
				return false;
			for (int i = 0; i < m_ParamSort.length; i++) {
				if (!params[i].equalsSort(m_ParamSort[i])
					&& (!mixRealInt || params[i] != getTheory().getSort("Int")))
					return false;
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
	public String toString() {
		StringBuffer sb = new StringBuffer();
		String name = PrintTerm.quoteIdentifier(m_Name);
		sb.append("(");
		if (m_Indices == null)
			sb.append(name);
		else {
			sb.append("(_ ").append(name);
			for (BigInteger i : m_Indices) {
				sb.append(" ").append(i);
			}
			sb.append(")");
		}
		for (Sort s : m_ParamSort) {
			sb.append(" ").append(s);
		}
		sb.append(" ").append(m_ReturnSort);
		sb.append(")");
		return sb.toString();
	}

	/**
	 * Checks if this function symbol was declared as chainable.
	 * This should only be true for the internal equality function.
	 * @return true if the function symbol is chainable.
	 */
	public boolean isChainable() {
		return (m_Flags & ASSOCMASK) == CHAINABLE;
	}
	/**
	 * Checks if this function symbol was declared as pairwise.
	 * This should only be true for the internal distinct function.
	 * @return true if the function symbol is pairwise.
	 */
	public boolean isPairwise() {
		return (m_Flags & ASSOCMASK) == PAIRWISE;
	}
	/**
	 * Checks if this function symbol was declared as left associative.
	 * This should only be true for internal function symbols.
	 * @return true if the function symbol is left associative.
	 */
	public boolean isLeftAssoc() {
		return (m_Flags & ASSOCMASK) == LEFTASSOC;
	}
	/**
	 * Checks if this function symbol was declared as right associative.
	 * This should only be true for internal function symbols.
	 * @return true if the function symbol is right associative.
	 */
	public boolean isRightAssoc() {
		return (m_Flags & ASSOCMASK) == RIGHTASSOC;
	}
	
	/**
	 * Checks if this function symbol was created with the SMTLIB
	 * syntax <code>(as name sort)</code> to give it a different result 
	 * sort.
	 * @return true if the sort was explicitly given, false if it is implicit.
	 */
	public boolean isReturnOverload() {
		return (m_Flags & RETURNOVERLOAD) != 0;
	}

	/**
	 * Get the string representation of this function symbol as it would
	 * be used to build an application term.
	 * @return the string representation.
	 */
	public String getApplicationString() {
		String name = PrintTerm.quoteIdentifier(m_Name);
		if (m_Indices == null && !isReturnOverload())
			return name;
		StringBuffer sb = new StringBuffer();
		if (isReturnOverload())
			sb.append("(as ");
		if (m_Indices != null)
			sb.append("(_ ");
		sb.append(name);
		if (m_Indices != null) {
			for (BigInteger i : m_Indices)
				sb.append(" ").append(i);
			sb.append(")");
		}
		if (isReturnOverload())
			sb.append(" ").append(getReturnSort()).append(")");
		return sb.toString();
	}
	/**
	 * Check whether this function symbol is an internal symbol that has a fixed
	 * semantic.
	 * @return true if and only if the symbol is an internal symbol with a fixed
	 *         semantic.
	 */
	public boolean isInterpreted() {
		return isIntern() && (!m_Name.startsWith("@") || !m_Name.endsWith("0"));
	}
}
