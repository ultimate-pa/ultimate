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
import java.util.ArrayDeque;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.util.HashUtils;

/**
 * Represents an smtlib sort.  We distinguish real sorts (which
 * are declared with declare-sort or pre-defined in the logic) from
 * defined sort (which are defined with define-sort to some other sort.
 * For a real sort, <tt>getRealSort() == this</tt> holds.
 * 
 * A sort has a sort symbol and as many sort arguments as the sort symbol
 * specifies.  There are also parametric sorts used for declaring polymorphic
 * function symbols.  A parametric sort (or sort variable) has a position
 * (used for substitution) and a name, both stored in the SortSymbol.
 * 
 * Every term has a closed real sort, which can be obtained by term.getSort().
 * Defined sorts may occur only in function symbols and the declared sort of
 * a term variable.  Sorts that are not closed may only occur in polymorphic
 * function symbols and in sort definitions in SortSymbol.
 * 
 * @author Jochen Hoenicke
 */
public class Sort {
	/**
	 * The sort symbol
	 */
	SortSymbol m_Symbol;
	/**
	 * The arguments of the sort symbol.  This is null if the sort symbol 
	 * has no arguments, otherwise it is an array with m_Symbol.m_numParams
	 * elements.
	 */
	Sort[]     m_Args;
	/**
	 * The indices of the sort symbol.  For the sort BitVec this is an
	 * array with one element containing the bit length.  This field is
	 * null (instead of the empty array) if there are no indices.
	 */
	BigInteger[] m_Indices;
	/**
	 * The cached real sort.  This is null if real sort was not yet computed.
	 * Otherwise it is this for a real sort and the real sort as which the
	 * sort is defined in all other cases.
	 */
	//@ invariant m_RealSort == null || m_RealSort.getRealSort() == m_RealSort
	Sort       m_RealSort;
	
	int m_Hash;
	
	Sort(SortSymbol sym, BigInteger[] indices, Sort[] args) {
		assert args.length == (sym.isParametric() ? 0 : sym.m_NumParams) 
				: "Sort created with wrong number of args";
		m_Symbol = sym;
		m_Indices = indices;
		m_Args = args;
		m_Hash = m_Symbol.hashCode();
		if (m_Args != null)
			m_Hash = HashUtils.hashJenkins(m_Hash, (Object[]) m_Args);
		if (m_Indices != null)
			m_Hash = HashUtils.hashJenkins(m_Hash, (Object[]) m_Indices);
	}
	
	/**
	 * Get the name of this sort.
	 * @return the name.
	 */
	public String getName() {
		return m_Symbol.getName();
	}

	/**
	 * Get the indexed name of this sort in smtlib representation.
	 * @return the name.
	 */
	public String getIndexedName() {
		String name = PrintTerm.quoteIdentifier(m_Symbol.getName());
		if (m_Indices == null)
			return name;
		StringBuilder sb = new StringBuilder();
		sb.append("(_ ").append(name);
		for (BigInteger i : m_Indices)
			sb.append(" ").append(i);
		sb.append(")");
		return sb.toString();
	}
	
	
	/**
	 * Get the indices, if this is an indexed sort like (_ bv 5).
	 * @return the indices, null if this sort is not indexed.
	 */
	public BigInteger[] getIndices() {
		return m_Indices;
	}
	
	public Sort[] getArguments() {
		return m_Args;
	}
	
	public Sort getRealSort() {
		if (m_RealSort == null) {
			if (m_Symbol.m_SortDefinition == null) {
				if (m_Args.length == 0) {
					m_RealSort = this;
				} else {
					Sort[] newArgs = m_Args;
					for (int i = 0; i < newArgs.length; i++) {
						Sort realArg = m_Args[i].getRealSort();
						if (realArg != m_Args[i]) {
							if (newArgs == m_Args)
								newArgs = m_Args.clone();
							newArgs[i] = realArg;
						}
					}
					if (newArgs == m_Args)
						m_RealSort = this;
					else
						m_RealSort = m_Symbol.getSort(m_Indices, newArgs).getRealSort();
				}
			} else {
				m_RealSort = 
					m_Symbol.m_SortDefinition.mapSort(m_Args).getRealSort();
			}
		}
		return m_RealSort;
	}
	
	boolean equalsSort(Sort other) {
		if (this == other)
			return true;
		return getRealSort() == other.getRealSort();
	}
	
	/**
	 * Unify this sort with a concrete sort.
	 * 
	 * @param unifier The unifier map. It serves as map from sort parameters 
	 * to substituted sorts, and also as cache for all open sorts.  It should
	 * contain all previously computed substitutions.
	 * @param concrete the concrete sort to unify this sort with.  
	 *        It must be closed and real.
	 * @return true if the sorts unify (in which case the unifier is extended)
	 * or false otherwise.
	 */
    boolean unifySort(HashMap<Sort,Sort> unifier, Sort concrete) {
    	assert concrete.getRealSort() == concrete;
		Sort last = unifier.get(this);
		if (last != null)
			return last == concrete;
		
		if (!m_Symbol.isParametric()) {
			Sort me = getRealSort();
			if (me.m_Symbol != concrete.m_Symbol)
				return false;

			for (int i = 0; i < me.m_Args.length; i++) {
				if (!me.m_Args[i].unifySort(unifier, concrete.m_Args[i]))
					return false;
			}
		}
		unifier.put(this, concrete);
		return true;
	}

	/**
	 * Substitute this sort.  
	 * 
	 * @param substitution The substitution. Note that every sort variable has
	 * a unique position which is used as index in the substitution array.
	 * @return The substituted sort.
	 */
    Sort mapSort(Sort[] substitution) {
		if (m_Symbol.isParametric())
			return substitution[m_Symbol.m_NumParams];
		if (m_Args.length == 0)
			return this;
    	if (m_Args.length == 1) {
    		Sort arg = m_Args[0].mapSort(substitution);
    		return m_Symbol.getSort(m_Indices, new Sort[] { arg });
    	}
    	
    	// For more than two arguments create a cache to avoid exponential blow
    	HashMap<Sort, Sort> cachedMappings = new HashMap<Sort,Sort>();
    	return mapSort(substitution, cachedMappings);
    }
    
	/**
	 * Substitute this sort.  
	 * 
	 * @param substitution The substitution. Note that every sort variable has
	 * a unique position which is used as index in the substitution array.
	 * @param cachedMappings A cache storing for each visited sort the 
	 * corresponding substituted sort.
	 * @return The substituted sort.
	 */
    Sort mapSort(Sort[] substitution, HashMap<Sort, Sort> cachedMappings) {
		if (m_Symbol.isParametric())
			return substitution[m_Symbol.m_NumParams];
    	Sort result = cachedMappings.get(this);
    	if (result != null)
    		return result;
    	if (m_Args.length != 0) {
			Sort[] newArgs = new Sort[m_Args.length];
			for (int i = 0; i < m_Args.length; i++) {
				newArgs[i] = m_Args[i].mapSort(substitution, cachedMappings);
			}
			result = m_Symbol.getSort(m_Indices, newArgs);
    	} else {
    		result = this;
    	}
		cachedMappings.put(this, result);
		return result;
	}

	public boolean isParametric() {
		return m_Symbol.isParametric();
	}

	public String toString() {
		if (m_Args.length == 0)
			return getIndexedName();
		StringBuilder sb = new StringBuilder();
		new PrintTerm().append(sb, this);
		return sb.toString();
	}
	
	/**
	 * Convert a sort to a string in a stack based fashion.
	 * @param m_Todo The stack where to put the strings and sub sorts.
	 * @see PrintTerm
	 */
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		String name = getIndexedName();
		Sort[] args = getArguments();
		if (args.length == 0) {
			m_Todo.addLast(name);
		} else {
			m_Todo.addLast(")");
			for (int i = args.length-1; i >= 0; i--) {
				m_Todo.addLast(args[i]);
				m_Todo.addLast(" ");
			}
			m_Todo.addLast(name);
			m_Todo.addLast("(");
		}
	}
	
	public Theory getTheory() {
		return m_Symbol.m_Theory;
	}

	public boolean isArraySort() {
		return getRealSort().m_Symbol.isArray();
	}
	public boolean isNumericSort() {
		return getRealSort().m_Symbol.isNumeric();
	}

	public boolean isInternal() {
		return m_Symbol.isIntern();
	}
	
	public int hashCode() {
		return m_Hash;
	}
}
