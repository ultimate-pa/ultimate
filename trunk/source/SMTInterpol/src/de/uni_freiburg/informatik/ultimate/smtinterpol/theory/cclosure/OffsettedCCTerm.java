/*
 * Copyright (C) 2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A {@link CCParameter} with a non-zero constant offset, i.e. the value {@code mTerm + mOffset}. Offset-free values are
 * represented by a bare {@link CCTerm}, so this class is only ever created with a non-zero offset (use
 * {@link CCParameter#of}).
 *
 * <p>{@code equals}/{@code hashCode} are structural over {@code (mTerm, mOffset)} (the term object and the offset),
 * which is stable. This is <em>not</em> the value identity {@code (representative, offsetToRep)} (which changes on
 * merge); for value comparison use {@link CCParameter#sameValueAs}.
 *
 * @author Jochen Hoenicke
 */
public final class OffsettedCCTerm implements CCParameter {
	private final CCTerm mTerm;
	private final Rational mOffset;

	OffsettedCCTerm(final CCTerm term, final Rational offset) {
		assert !offset.equals(Rational.ZERO) : "use a bare CCTerm for a zero offset";
		mTerm = term;
		mOffset = offset;
	}

	@Override
	public CCTerm getCCTerm() {
		return mTerm;
	}

	@Override
	public Rational getOffset() {
		return mOffset;
	}

	@Override
	public Term getFlatTerm() {
		final Term term = mTerm.getFlatTerm();
		return CCParameter.addConstant(term, mOffset);
	}

	@Override
	public int hashCode() {
		return mTerm.hashCode() * 31 + mOffset.hashCode();
	}

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (!(other instanceof OffsettedCCTerm)) {
			return false;
		}
		final OffsettedCCTerm o = (OffsettedCCTerm) other;
		return mTerm == o.mTerm && mOffset.equals(o.mOffset);
	}

	@Override
	public String toString() {
		return mTerm + "+" + mOffset;
	}
}
