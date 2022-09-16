/*
 * Copyright (C) 2009-2021 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.proof;

import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * Class representing a literal in the minimal proof format. A literal is an
 * SMTLIB term with a polarity.
 *
 * @author Jochen Hoenicke
 */
public class ProofLiteral {
	Term mAtom;
	boolean mPositive;

	public ProofLiteral(final Term atom, final boolean positive) {
		mAtom = atom;
		mPositive = positive;
	}

	/**
	 * Get the polarity of the literal.
	 *
	 * @return true if positive, false if negative.
	 */
	public boolean getPolarity() {
		return mPositive;
	}

	/**
	 * Get the atom of the literal.
	 *
	 * @return the atom as an SMTLIB term.
	 */
	public Term getAtom() {
		return mAtom;
	}

	public ProofLiteral negate() {
		return new ProofLiteral(mAtom, !mPositive);
	}

	@Override
	public int hashCode() {
		return mAtom.hashCode() ^ (mPositive ? 0 : 0xffffffff);
	}

	@Override
	public boolean equals(final Object other) {
		if (!(other instanceof ProofLiteral)) {
			return false;
		}
		final ProofLiteral otherLit = (ProofLiteral) other;
		return mAtom == otherLit.mAtom && mPositive == otherLit.mPositive;
	}

	@Override
	public String toString() {
		return (mPositive ? "+ " : "- ") + mAtom.toString();
	}
}