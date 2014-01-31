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
 * An interpretation for a sort.  This can either be finite or infinite.  If it
 * is finite, it should be able to produce an enumeration of all elements in the
 * interpretation.  Otherwise, it should return a homomorphism to either the
 * integers or the reals.
 * @author Juergen Christ
 */
public interface SortInterpretation {
	/**
	 * Is the interpretation for this sort finite.
	 * @return Is the interpretation for this sort finite.
	 */
	public boolean isFinite();
	/**
	 * Add a term to the interpretation of this sort.
	 * @param termOfSort Term to add.
	 */
	public void extend(Term termOfSort);
	/**
	 * Convert this sort interpretation to SMTLIB.
	 * @param t    Theory to use during conversion.
	 * @param sort The sort described by this interpretation.
	 * @return Formula describing the representation of the interpretation.
	 */
	public Term toSMTLIB(Theory t, Sort sort);
	/**
	 * Return an element of this sort.  This might return <code>null</code> only
	 * if there is no element of this sort known until now.
	 * @return An element of this sort or <code>null</code>.
	 */
	public Term peek();
	/**
	 * Build a constraint for a given term to satisfy this sort interpretation.
	 * @param input Term to constrain.
	 * @return The constraint.
	 */
	public Term constrain(Theory t, Term input);
}
