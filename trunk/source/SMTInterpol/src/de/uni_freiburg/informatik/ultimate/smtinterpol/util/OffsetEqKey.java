/*
 * Copyright (C) 2009-2026 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.util;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * A lookup key identifying an (offset) equality by the affine fact it expresses:
 * the offset-free parts of its two sides (see {@link OffsetTerm}) together with
 * the constant offset {@code constant(lhs) - constant(rhs)} between them. Two
 * equalities with the same key denote the same fact {@code lhs = rhs}, which is
 * what lets a needed equality like {@code (= (+ x 5) (+ y 7))} be matched against
 * the clause literal {@code (= x (+ y 2))}. The two offset-free parts are kept
 * <em>separate</em> (rather than subtracted into one difference polynomial) so
 * that unrelated edges whose difference polynomials coincide up to sign — e.g.
 * {@code x+y = z+w+2} and {@code z-y = x-w-2} — do not collide.
 *
 * <p>Splitting only happens when offset equalities are enabled, mirroring the clausifier, which then represents a
 * numeric term as an offset-free term plus a constant. Without them a constant stays part of the term, so
 * {@code 0 = 1} and {@code 1 = 2} are two facts, as the terms and the proof generator see them, and every key has
 * offset zero.
 */
public final class OffsetEqKey {
	private final Term mLhs;
	private final Term mRhs;
	private final Rational mLhsOffset;
	private final Rational mOffset;
	private final int mHash;

	/**
	 * Build the key for the equality {@code lhs = rhs}.
	 *
	 * @param splitOffsets whether offset equalities are enabled, i.e. whether a numeric term is split into an
	 *                     offset-free part and a constant.
	 */
	public OffsetEqKey(final Term lhs, final Term rhs, final boolean splitOffsets) {
		if (splitOffsets && lhs.getSort().isNumericSort()) {
			final OffsetTerm lhsSplit = new OffsetTerm(lhs);
			final OffsetTerm rhsSplit = new OffsetTerm(rhs);
			mLhs = lhsSplit.getTerm();
			mRhs = rhsSplit.getTerm();
			mLhsOffset = lhsSplit.getOffset();
			mOffset = lhsSplit.getOffset().sub(rhsSplit.getOffset());
		} else {
			mLhs = lhs;
			mRhs = rhs;
			mLhsOffset = Rational.ZERO;
			mOffset = Rational.ZERO;
		}
		final int lhsHash = mLhs.hashCode();
		final int rhsHash = mRhs.hashCode();
		if (lhsHash == rhsHash) {
			mHash = lhsHash * 31 + mOffset.abs().hashCode();
		} else if (lhsHash < rhsHash) {
			mHash = lhsHash * 37 + rhsHash * 31 + mOffset.hashCode();
		} else {
			mHash = rhsHash * 37 + lhsHash * 31 + mOffset.negate().hashCode();
		}
	}

	public Term getLhs() {
		return mLhs;
	}

	public Term getRhs() {
		return mRhs;
	}

	public Rational getOffset() {
		return mOffset;
	}

	/**
	 * The absolute offset of the lhs term this key was built from, i.e. {@code lhs = getLhs() + getLhsOffset()}.
	 */
	public Rational getLhsOffset() {
		return mLhsOffset;
	}

	/**
	 * The absolute offset of the rhs term this key was built from, i.e. {@code rhs = getRhs() + getRhsOffset()}.
	 */
	public Rational getRhsOffset() {
		return mLhsOffset.sub(mOffset);
	}

	/**
	 * Check whether this key matches the given equal key with swapped sides, i.e. whether the lhs this key was built
	 * from corresponds to the rhs of {@code other}.
	 *
	 * @param other a key that is {@code equals} to this key.
	 */
	public boolean isSwapped(final OffsetEqKey other) {
		assert equals(other);
		return !(mLhs == other.mLhs && mOffset.equals(other.mOffset));
	}

	/**
	 * Compute the constant shift between the equality this key was built from and the equality the given equal key
	 * was built from. If {@code other} was built from {@code l = r}, then this key was built from an equality
	 * {@code l + shift = r + shift} (modulo swapping of sides).
	 *
	 * @param other a key that is {@code equals} to this key.
	 * @return the shift such that the sides of this key's equality are the sides of {@code other}'s equality plus
	 *         the shift.
	 */
	public Rational getShift(final OffsetEqKey other) {
		assert equals(other);
		return mLhsOffset.sub(isSwapped(other) ? other.getRhsOffset() : other.getLhsOffset());
	}

	@Override
	public int hashCode() {
		return mHash;
	}

	@Override
	public boolean equals(final Object other) {
		if (this == other) {
			return true;
		}
		if (!(other instanceof OffsetEqKey)) {
			return false;
		}
		final OffsetEqKey o = (OffsetEqKey) other;
		return (mOffset.equals(o.mOffset) && mLhs == o.mLhs && mRhs == o.mRhs)
				|| (mOffset.equals(o.mOffset.negate()) && mLhs == o.mRhs && mRhs == o.mLhs);
	}
}
