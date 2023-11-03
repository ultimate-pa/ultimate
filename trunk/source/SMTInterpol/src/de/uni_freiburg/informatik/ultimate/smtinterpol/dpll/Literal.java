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
package de.uni_freiburg.informatik.ultimate.smtinterpol.dpll;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;


public abstract class Literal implements ILiteral {
	DPLLAtom mAtom;
	protected Literal  mNegated;
	Clause.WatchList mWatchers = new Clause.WatchList();

	private final int mHash;
	@Override
	public final int hashCode() {
		return mHash;
	}

	public Literal(int hash) {
		mHash = hash;
	}

	/**
	 * Returns the underlying atom.  If this literal is an atom, it returns
	 * itself.
	 */
	@Override
	public final DPLLAtom getAtom() { return mAtom; } // NOCHECKSTYLE
	/**
	 * Returns the negated literal.
	 */
	@Override
	public final Literal  negate()  { return mNegated; } // NOCHECKSTYLE

	/**
	 * Returns true, as Literal is ground.
	 */
	@Override
	public final boolean isGround() {
		return true;
	}
	/**
	 * Returns the sign of the literal (1 for atom, -1 for negated atom).
	 */
	public abstract int getSign();
	
	/**
	 * Returns an SMT representation of the literal.
	 * @param smtTheory The term factory to use.
	 *
	 * @return an SMT representation of the literal.
	 */
	@Override
	public abstract Term getSMTFormula(Theory smtTheory);
}
