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
package de.uni_freiburg.informatik.ultimate.smtinterpol.interpolate;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, where the x_i are initially nonbasic variable.
 *
 * @author Jochen Hoenicke.
 */
public class InterpolatorAffineTerm {
	final SMTAffineTerm mAffine;
	int mEpsilon;

	public InterpolatorAffineTerm() {
		mAffine = new SMTAffineTerm();
		mEpsilon = 0;
	}

	public InterpolatorAffineTerm(final InterpolatorAffineTerm iat) {
		mAffine = new SMTAffineTerm();
		mAffine.add(iat.mAffine);
		mEpsilon = iat.mEpsilon;
	}

	public InterpolatorAffineTerm(final SMTAffineTerm affine) {
		mAffine = new SMTAffineTerm();
		mAffine.add(affine);
		mEpsilon = 0;
	}

	public void add(final Rational c) {
		mAffine.add(c);
	}

	public void add(final InfinitesimalNumber c) {
		mAffine.add(c.mReal);
		mEpsilon += c.mEps;
	}

	public void add(final Rational c, final Term term) {
		mAffine.add(c, term);
	}

	public void add(final Rational c, final InterpolatorAffineTerm a) {
		mAffine.add(c, a.mAffine);
		mEpsilon += c.signum() * a.mEpsilon;
	}

	public void mul(final Rational c) {
		mAffine.mul(c);
		mEpsilon *= c.signum();
	}

	public void negate() {
		mAffine.negate();
		mEpsilon = -mEpsilon;
	}

	public boolean isConstant() {
		return mAffine.isConstant();
	}

	public InfinitesimalNumber getConstant() {
		return new InfinitesimalNumber(mAffine.getConstant(), mEpsilon);
	}

	public Map<Term, Rational> getSummands() {
		return mAffine.getSummands();
	}

	public Rational getGcd() {
		return mAffine.getGcd();
	}

	@Override
	public String toString() {
		return mAffine.toString() + (mEpsilon == 0 ? "" : mEpsilon < 0 ? " - eps" : " + eps");
	}

	/**
	 * Convert the affine term to a term in our core theory.
	 */
	public Term toSMTLib(final Theory t, final boolean isInt) {
		assert (mEpsilon == 0);
		final Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		return mAffine.toTerm(numSort);
	}

	public boolean isInt() {
		for (final Term v : getSummands().keySet()) {
			if (!v.getSort().getName().equals("Int")) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Create the term <code>this <= val</code>.
	 *
	 * @param t
	 *            Theory used in conversion.
	 * @return A term for <code>this <= val</code>.
	 */
	public Term toLeq0(final Theory t) {
		assert (mEpsilon >= 0);
		if (isConstant()) {
			return getConstant().compareTo(InfinitesimalNumber.ZERO) <= 0 ? t.mTrue : t.mFalse;
		}
		final SMTAffineTerm left = new SMTAffineTerm();
		final SMTAffineTerm right = new SMTAffineTerm();
		final Sort numSort = isInt() ? t.getSort("Int") : t.getSort("Real");
		for (final Map.Entry<Term, Rational> entry : getSummands().entrySet()) {
			final Rational coeff = entry.getValue();
			if (coeff.signum() < 0) {
				right.add(coeff.negate(), entry.getKey());
			} else {
				left.add(coeff, entry.getKey());
			}
		}
		right.add(mAffine.getConstant().negate());
		return t.term(mEpsilon == 0 ? "<=" : "<", left.toTerm(numSort), right.toTerm(numSort));
	}

	@Override
	public int hashCode() {
		return mAffine.hashCode() + 1021 * mEpsilon;
	}
}
