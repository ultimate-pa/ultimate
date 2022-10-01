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
	 * Get some model value for the sort interpretation. This is what the model constant {@literal @}idx evaluates to.
	 *
	 * @return Index.
	 */
	public Term getModelValue(int index, Sort sort);

	/**
	 * Add a fresh distinct term to the sort interpretation.
	 *
	 * @return Index of the fresh element.
	 */
	public Term extendFresh(Sort sort);

	/**
	 * Tells the sort that this value is in use. This ensures that later calls of
	 * extendFresh will not return the same value again.
	 */
	public void register(Term value);

	/**
	 * Convert this sort interpretation to SMTLIB.
	 * @param t    Theory to use during conversion.
	 * @param sort The sort described by this interpretation.
	 * @return Formula describing the representation of the interpretation.
	 */
	public Term toSMTLIB(Theory t, Sort sort);
}
