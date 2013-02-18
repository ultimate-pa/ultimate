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
import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.util.UnifyHash;


public class SortSymbol {
	/**
	 * Flag to indicate that this is an internal sort symbol.  An internal
	 * sort is one, that is defined by the theory, i.e., Bool, Int, Real,
	 * BitVec, Array.
	 */
	public static final int INTERNAL  = 1;
	/**
	 * Flag to indicate that this sort is really a sort variable.  Sort
	 * variables are only used in sort definitions.  Outside of these every
	 * sort should not contain any sort variable. 
	 */
	public static final int TYPEPARAM = 2;
	/**
	 * Flag to indicate that this sort expects index parameter.  The only
	 * such sort is currently BitVec.
	 */
	public static final int INDEXED   = 4;
	/**
	 * Flag to indicate numeric types.
	 */
	public static final int NUMERIC   = 8;
	/**
	 * Flag to indicate array types.
	 */
	public static final int ARRAY     = 0x10;
	
	Theory m_Theory;
	String m_Name;
	/**
	 * The number of parameters this sort symbol expects.  If the TYPEPARAM
	 * flag is set, this sort is a sort variable and takes no parameters; in
	 * that case this gives the de-Bruijn-index of the sort variable.
	 */
	int m_NumParams;
	/**
	 * The flags.  This is the bitwise or of INTERNAL, TYPEPARAM and 
	 * INDEXED.
	 */
	int m_Flags;
	/**
	 * The sorts already created from this SortSymbol.
	 * If m_NumParams is 0, this is the single sort corresponding to
	 * this SortSymbol.  Otherwise this is a UnifyHash containing all
	 * created sorts.
	 */
	Object m_Sorts;
	
	/** 
	 * The primitive sort if this is a sort definition.
	 */
	Sort m_SortDefinition;
	
	/**
	 * The constructor for sort symbols.
	 * @param theory  The theory this sort belongs to.
	 * @param name    The name of the sort (without enclosing | for quoting).
	 * @param numParams The number of sort parameters this sort expects.
	 *                E.g., Array expects two sort parameters for index and
	 *                element sort.  For sort variables this gives the 
	 *                de-Bruijn index of the variable instead. 
	 * @param definition The sort definition, or null if this is a fresh sort.
	 * @param flags The flags; bitwise or of INTERNAL, TYPEPARAM and INDEXED.
	 */
	SortSymbol(Theory theory, String name, int numParams, 
			   Sort definition, int flags) {
		m_Theory = theory;
		m_Name = name;
		m_Flags = flags;
		m_NumParams = numParams;
		m_SortDefinition = definition;
		if ((m_Flags & TYPEPARAM) != 0
			|| ((m_Flags & INDEXED) == 0 && m_NumParams == 0)) {
			m_Sorts = new Sort(this, null, new Sort[0]);
		} else {
			m_Sorts = new UnifyHash<Sort>();
		}
	}
	
	/**
	 * Checks if the sort is internal, i.e., defined by the logic.
	 * @return true, if the sort is an internal sort.
	 */
	public boolean isIntern() {
		return (m_Flags & INTERNAL) != 0;
	}
	
	/**
	 * Returns the name of this sort.  The | symbols used for quoting are
	 * not part of the name.
	 * @return the name of the sort.
	 */
	public String getName() {
		return m_Name;
	}
	
	/**
	 * Returns a string representation of the sort symbol, as it would be
	 * used for declare-sort command.
	 * @return the string representation.
	 */
	public String toString() {
		return "(" + PrintTerm.quoteIdentifier(m_Name) + " " + m_NumParams + ")";
	}
	
	/**
	 * Checks whether the indices and the arity match and the sort can be
	 * created.  This function is called when a sort expression is parsed.
	 * Override this function if your sort expects indices.
	 * @param indices The indices.
	 * @param arity The number of sort parameters.
	 * @throws IllegalArgumentException if the sort parameters or the index
	 * do not match.
	 */
	public void checkArity(BigInteger[] indices, int arity) {
		if (indices != null)
			throw new IllegalArgumentException("Indexed Sort "+m_Name+" undefined");
		if (arity != ((m_Flags & TYPEPARAM) != 0 ? 0 : m_NumParams))
				throw new IllegalArgumentException
					("Wrong number of arguments for sort "+m_Name);
	}

	@SuppressWarnings("unchecked")
	/**
	 * Create the sort with the given indices and sort parameters. Sorts are
	 * unified, so this will return an instance of a previously created sort
	 * if it already exists.
	 * @param indices The indices of the sort, which are given by 
	 *                (_ sortname indices).  This is null if no indices were
	 *                used.
	 * @param args The sort parameters; the empty array if no parameters were used.
	 * @return the created sort.
	 * @throws IllegalArgumentException if the indices or number of sort
	 * parameters do not match.
	 */
	public Sort getSort(BigInteger[] indices, Sort... args) {
		checkArity(indices, args.length);
		if ((m_Flags & INDEXED) == 0 && args.length == 0)
			return (Sort) m_Sorts;
		UnifyHash<Sort> sortCache = (UnifyHash<Sort>) m_Sorts;
		int hash = Arrays.hashCode(indices) ^ Arrays.hashCode(args);
		for (Sort sort : sortCache.iterateHashCode(hash)) {
			if (Arrays.equals(sort.getArguments(), args)
				&& Arrays.equals(sort.getIndices(), indices)) {
				return sort;
			}
		}
		Sort sort = new Sort(this, indices, args);
		sortCache.put(hash, sort);
		return sort;
	}

	/**
	 * Checks if this is a sort variable.
	 * @return true if this is a sort variable.
	 */
	public boolean isParametric() {
		return (m_Flags & TYPEPARAM) != 0;
	}
	/**
	 * Check if this sort symbol corresponds to a numeric sort.
	 * @return true if this sort is numeric.
	 */
	public boolean isNumeric() {
		return (m_Flags & NUMERIC) != 0;
	}
	/**
	 * Check if this sort symbol corresponds to an array sort.
	 * @return true if this sort is an array sort.
	 */
	public boolean isArray() {
		return (m_Flags & ARRAY) != 0;
	}
	
	public int hashCode() {
		return m_Name.hashCode();
	}
}
