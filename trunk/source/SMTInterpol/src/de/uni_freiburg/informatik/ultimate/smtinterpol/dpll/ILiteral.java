/*
 * Copyright (C) 2019 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * @author Tanja Schindler
 */
public interface ILiteral {

	/**
	 * Get the underlying atom of this literal.
	 *
	 * @return the underlying atom. If this literal is an atom, it returns itself.
	 */
	public ILiteral getAtom();

	/**
	 * Return the negated literal.
	 */
	public ILiteral negate();

	/**
	 * Check if the literal is ground.
	 *
	 * @return true if it is a ground literal, false otherwise.
	 */
	public boolean isGround();

	/**
	 * Returns an SMT representation of the literal.
	 *
	 * @param theory
	 *            The term factory to use.
	 * @return an SMT representation of the literal.
	 */
	public Term getSMTFormula(final Theory theory);

	@Override
	public String toString();
}
