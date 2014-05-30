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
package de.uni_freiburg.informatik.ultimate.smtinterpol.model;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * An interpretation for a sort.  We represent a sort as an enumeration of its
 * elements.  The elements are represented by model values
 * (<code>(as {@literal @}n T)</code> for a numeral n and a type T in SMTLIB).
 * @author Juergen Christ
 */
public interface SortInterpretation {
	/**
	 * Ensure the sort interpretation contains at least a specified number of
	 * distinct elements.
	 * @param numValues The minimum number of elements required for this sort.
	 * @return Total number of elements stored in this interpretation.
	 */
	public int ensureCapacity(int numValues);
	/**
	 * Add a fresh distinct term to the sort interpretation.
	 * @return Index of the fresh element.
	 */
	public int extendFresh();
	/**
	 * Returns the number of distinct elements of this sort.
	 * @return The number of distinct elements of this sort.
	 */
	public int size();
	/**
	 * Get a term corresponding to the index.
	 * @param idx Non-negative index of the element.
	 * @param s   Sort of the result term.
	 * @param t   Theory used to generate the result term.
	 * @return A term corresponding to the index.
	 * @throws IndexOutOfBoundsException If the index is not valid.
	 */
	public Term get(int idx, Sort s, Theory t) throws IndexOutOfBoundsException;
	/**
	 * Convert this sort interpretation to SMTLIB.
	 * @param t    Theory to use during conversion.
	 * @param sort The sort described by this interpretation.
	 * @return Formula describing the representation of the interpretation.
	 */
	public Term toSMTLIB(Theory t, Sort sort);
}
