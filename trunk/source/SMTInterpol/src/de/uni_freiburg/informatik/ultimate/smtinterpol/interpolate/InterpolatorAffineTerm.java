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

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitesimalNumber;

/**
 * Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, where the x_i are initially nonbasic variable.
 *
 * @author hoenicke.
 */
public class InterpolatorAffineTerm {
	Map<Term, Rational> mSummands = new HashMap<>();
	InfinitesimalNumber mConstant;

	public InterpolatorAffineTerm() {
		mConstant = InfinitesimalNumber.ZERO;
	}

	public InterpolatorAffineTerm(final InterpolatorAffineTerm iat) {
		mConstant = iat.getConstant();
		mSummands.putAll(iat.getSummands());
	}

	public InterpolatorAffineTerm(final SMTAffineTerm affine) {
		mConstant = new InfinitesimalNumber(affine.getConstant(), 0);
		mSummands.putAll(affine.getSummands());
	}

	public InterpolatorAffineTerm add(final Rational c) {
		mConstant = mConstant.add(new InfinitesimalNumber(c, 0));
		return this;
	}

	public InterpolatorAffineTerm add(final InfinitesimalNumber c) {
		mConstant = mConstant.add(c);
		return this;
	}

	public InterpolatorAffineTerm add(final Rational c, final Term term) {
		if (!c.equals(Rational.ZERO)) {
			addSimple(c, term);
		}
		return this;
	}

	private void addMap(final Rational c, final Map<Term, Rational> linterm) {
		for (final Map.Entry<Term, Rational> summand : linterm.entrySet()) {
			addSimple(c.mul(summand.getValue()), summand.getKey());
		}
	}

	private void addSimple(Rational c, final Term term) {
		assert (/* !term.getLinVar().isInitiallyBasic() && */ !c.equals(Rational.ZERO));
		final Rational oldc = mSummands.remove(term);
		if (oldc != null) {
			c = oldc.add(c);
			if (c.equals(Rational.ZERO)) {
				return;
			}
		}
		mSummands.put(term, c);
	}

	public InterpolatorAffineTerm add(final Rational c, final InterpolatorAffineTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.mSummands);
			mConstant = mConstant.add(a.mConstant.mul(c));
		}
		return this;
	}

	public InterpolatorAffineTerm mul(final Rational c) {
		if (c.equals(Rational.ZERO)) {
			mSummands.clear();
		} else if (!c.equals(Rational.ONE)) {
			for (final Map.Entry<Term, Rational> summand : mSummands.entrySet()) {
				summand.setValue(c.mul(summand.getValue()));
			}
			mConstant = mConstant.mul(c);
		}
		return this;
	}

	public InterpolatorAffineTerm div(final Rational c) {
		return mul(c.inverse());
	}

	public InterpolatorAffineTerm negate() {
		return mul(Rational.MONE);
	}

	public boolean isConstant() {
		return mSummands.isEmpty();
	}

	public InfinitesimalNumber getConstant() {
		return mConstant;
	}

	public Map<Term, Rational> getSummands() {
		return mSummands;
	}

	public Rational getGCD() {
		assert (!mSummands.isEmpty());
		final Iterator<Rational> it = mSummands.values().iterator();
		Rational gcd = it.next();
		final boolean firstSign = gcd.isNegative();
		gcd = gcd.abs();
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		if (firstSign) {
			gcd = gcd.negate();
		}
		return gcd;
	}

	/**
	 * For integer valued interpolants, convert Rationals to integer valued Rational by dividing by the rational
	 * greatest common divisor.
	 */
	void normalize() {
		mul(getGCD().inverse());
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		boolean isFirst = true;
		for (final Entry<Term, Rational> entry : mSummands.entrySet()) {
			final Term var = entry.getKey();
			Rational fact = entry.getValue();
			if (fact.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(Rational.ONE)) {
				sb.append(fact).append('*');
			}
			sb.append(var);
			isFirst = false;
		}
		if (isFirst) {
			sb.append(mConstant);
		} else {
			final int signum = mConstant.compareTo(InfinitesimalNumber.ZERO);
			if (signum < 0) {
				sb.append(" - ");
				sb.append(mConstant.mul(Rational.MONE));
			} else if (signum > 0) {
				sb.append(" + ");
				sb.append(mConstant);
			}
		}
		return sb.toString();
	}

	/**
	 * Convert the affine term to a term in our core theory.
	 */
	public Term toSMTLib(final Theory t, final boolean isInt) {
		assert (mConstant.mEps == 0);
		final Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		return new SMTAffineTerm(mSummands, mConstant.mReal).toTerm(numSort);
	}

	public boolean isInt() {
		for (final Term v : mSummands.keySet()) {
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
		assert (mConstant.mEps >= 0);
		if (isConstant()) {
			return mConstant.compareTo(InfinitesimalNumber.ZERO) <= 0 ? t.mTrue : t.mFalse;
		}
		final SMTAffineTerm left = new SMTAffineTerm();
		final SMTAffineTerm right = new SMTAffineTerm();
		final Sort numSort = isInt() ? t.getSort("Int") : t.getSort("Real");
		for (final Map.Entry<Term, Rational> entry : mSummands.entrySet()) {
			final Rational coeff = entry.getValue();
			if (coeff.signum() < 0) {
				right.add(coeff.negate(), entry.getKey());
			} else {
				left.add(coeff, entry.getKey());
			}
		}
		right.add(mConstant.mReal.negate());
		return t.term(mConstant.mEps == 0 ? "<=" : "<", left.toTerm(numSort), right.toTerm(numSort));
	}

	@Override
	public int hashCode() {
		return mConstant.hashCode() + 1021 * mSummands.hashCode();
	}
}
