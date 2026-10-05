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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.LitInfo;
import de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate.Interpolator.Occurrence;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.OffsetEqKey;
import de.uni_freiburg.informatik.ultimate.smtinterpol.util.Polynomial;

/**
 * The {@link LitInfo} of an (offset) equality literal together with the offset shift and orientation between the
 * literal and the concrete instance in which it is used, e.g. a path step in a CC lemma. If the literal is
 * {@code l = r}, the instance is {@code l + shift = r + shift} (with sides possibly swapped). The mixed variable of
 * the literal names the shared value of {@code l} and {@code r}; at instance level it therefore stands for
 * {@code mixedVar + shift}, see {@link #getMixedBoundary()}. Conversely, an {@code EQ} placeholder equating the
 * mixed variable with an instance-level shared term must subtract the shift from that term, see
 * {@link #buildEQ(Term)}.
 */
public class OffsetLitInfo {
	private final Theory mTheory;
	private final OffsetEqKey mLitKey;
	private final LitInfo mLitInfo;
	private final Rational mShift;
	private final boolean mSwapped;

	/**
	 * Create the info for an equality literal itself, i.e. with zero shift and unswapped sides.
	 *
	 * @param theory  the SMT theory.
	 * @param litInfo the occurrence info of the literal.
	 * @param litKey  the key built from the literal's own lhs and rhs.
	 */
	public OffsetLitInfo(final Theory theory, final LitInfo litInfo, final OffsetEqKey litKey) {
		this(theory, litInfo, litKey, Rational.ZERO, false);
	}

	private OffsetLitInfo(final Theory theory, final LitInfo litInfo, final OffsetEqKey litKey, final Rational shift,
			final boolean swapped) {
		mTheory = theory;
		mLitInfo = litInfo;
		mLitKey = litKey;
		mShift = shift;
		mSwapped = swapped;
	}

	/**
	 * Derive the info for a concrete instance of the literal, computing the shift and orientation of the instance
	 * relative to the literal.
	 *
	 * @param instanceKey the key built from the instance's left and right side; must be {@code equals} to the
	 *                    literal's key.
	 */
	public OffsetLitInfo reorient(final OffsetEqKey instanceKey) {
		final Rational shift = instanceKey.getShift(mLitKey);
		final boolean swapped = instanceKey.isSwapped(mLitKey);
		if (shift.equals(mShift) && swapped == mSwapped) {
			return this;
		}
		return new OffsetLitInfo(mTheory, mLitInfo, mLitKey, shift, swapped);
	}

	public LitInfo getLitInfo() {
		return mLitInfo;
	}

	public TermVariable getMixedVar() {
		return mLitInfo.getMixedVar();
	}

	public Rational getShift() {
		return mShift;
	}

	public boolean isALocal(final int partition) {
		return mLitInfo.isALocal(partition);
	}

	public boolean isBLocal(final int partition) {
		return mLitInfo.isBLocal(partition);
	}

	public boolean isAorShared(final int partition) {
		return mLitInfo.isAorShared(partition);
	}

	public boolean isBorShared(final int partition) {
		return mLitInfo.isBorShared(partition);
	}

	public boolean isMixed(final int partition) {
		return mLitInfo.isMixed(partition);
	}

	/**
	 * Check whether the left side of the instance is A-local. This is the literal's lhs occurrence corrected for
	 * the instance's orientation. Only meaningful for partitions where the literal is mixed.
	 */
	public boolean isLeftALocal(final int partition) {
		final Occurrence lhsOccur = mLitInfo.getLhsOccur();
		return mSwapped ? lhsOccur.isBLocal(partition) : lhsOccur.isALocal(partition);
	}

	/**
	 * Check whether the left side of the instance is B-local. This is the literal's lhs occurrence corrected for
	 * the instance's orientation. Only meaningful for partitions where the literal is mixed.
	 */
	public boolean isLeftBLocal(final int partition) {
		final Occurrence lhsOccur = mLitInfo.getLhsOccur();
		return mSwapped ? lhsOccur.isALocal(partition) : lhsOccur.isBLocal(partition);
	}

	/**
	 * The mixed variable lifted to instance level, i.e. {@code mixedVar + shift}. This is the shared boundary term
	 * for the instance of the mixed literal. The result is in normal form, since the mixed variable is a plain
	 * term variable and the constant comes last.
	 */
	public Term getMixedBoundary() {
		final TermVariable mixedVar = mLitInfo.getMixedVar();
		if (mShift.equals(Rational.ZERO)) {
			return mixedVar;
		}
		return mTheory.term("+", mixedVar, mShift.toTerm(mixedVar.getSort()));
	}

	/**
	 * Build the placeholder {@code EQ(mixedVar, sharedTerm - shift)}. The shared term is given at instance level;
	 * subtracting the shift moves it to the literal level at which the mixed variable lives. The subtraction is
	 * normalized, as the shared term may itself be a sum or a constant.
	 *
	 * @param sharedTerm the instance-level shared term the mixed variable should be equated with.
	 */
	public Term buildEQ(final Term sharedTerm) {
		Term shifted = sharedTerm;
		if (!mShift.equals(Rational.ZERO)) {
			final Polynomial poly = new Polynomial(sharedTerm);
			poly.add(mShift.negate());
			shifted = poly.toTerm(sharedTerm.getSort());
		}
		return mTheory.term(Interpolator.EQ, mLitInfo.getMixedVar(), shifted);
	}
}
