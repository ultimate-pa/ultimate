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

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.convert.SMTAffineTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.InfinitNumber;

/**
 * Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, where the x_i are initially nonbasic variable.
 *
 * @author hoenicke.
 */
public class InterpolatorAffineTerm {
	Map<Term, Rational> mSummands = new HashMap<>();
	InfinitNumber mConstant;

	public InterpolatorAffineTerm() {
		mConstant = InfinitNumber.ZERO;
	}

	public InterpolatorAffineTerm(final InterpolatorAffineTerm iat) {
		mConstant = iat.getConstant();
		mSummands.putAll(iat.getSummands());
	}

	public InterpolatorAffineTerm(final SMTAffineTerm affine) {
		mConstant = new InfinitNumber(affine.getConstant(), 0);
		mSummands.putAll(affine.getSummands());
	}

	public InterpolatorAffineTerm add(final Rational c) {
		mConstant = mConstant.add(new InfinitNumber(c, 0));
		return this;
	}

	public InterpolatorAffineTerm add(final InfinitNumber c) {
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

	public InfinitNumber getConstant() {
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
			final int signum = mConstant.compareTo(InfinitNumber.ZERO);
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
		assert (numSort != null);
		final Sort[] binfunc = new Sort[] { numSort, numSort };
		final FunctionSymbol times = t.getFunction("*", binfunc);
		final FunctionSymbol plus = t.getFunction("+", binfunc);
		FunctionSymbol negate = t.getFunction("-", numSort);
		if (negate == null) {
			negate = t.getFunction("-", numSort);
		}
		assert (!isInt || mConstant.mA.isIntegral());
		Term comb = mConstant.mA.equals(Rational.ZERO) ? null : mConstant.mA.toTerm(numSort);
		for (final Map.Entry<Term, Rational> me : mSummands.entrySet()) {
			Term convme = me.getKey();
			// if affine term is integral it may only add integers.
			assert (!isInt || convme.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && convme.getSort().getName().equals("Int")) {
				final Sort intSort = t.getSort("Int");
				final FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE)) {
				convme = t.term(negate, convme);
			} else if (!me.getValue().equals(Rational.ONE)) {
				final Term convfac = me.getValue().toTerm(numSort);
				convme = t.term(times, convfac, convme);
			}
			if (comb == null) {
				comb = convme;
			} else {
				comb = t.term(plus, convme, comb);
			}
		}
		if (comb == null) {
			return Rational.ZERO.toTerm(numSort);
		}
		return comb;
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
			return mConstant.compareTo(InfinitNumber.ZERO) <= 0 ? t.mTrue : t.mFalse;
		}
		final boolean isInt = isInt();
		final Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert (numSort != null);
		final Sort[] binfunc = new Sort[] { numSort, numSort };
		final FunctionSymbol times = t.getFunction("*", binfunc);
		final ArrayList<Term> lcomb = new ArrayList<>();
		final ArrayList<Term> rcomb = new ArrayList<>();
		for (final Map.Entry<Term, Rational> me : mSummands.entrySet()) {
			Term convme = me.getKey();
			// if affine term is integral it may only add integers.
			assert (!isInt || convme.getSort().getName().equals("Int"));
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && convme.getSort().getName().equals("Int")) {
				final Sort intSort = t.getSort("Int");
				final FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (me.getValue().equals(Rational.MONE)) {
				rcomb.add(convme);
			} else if (me.getValue().signum() < 0) {
				final Term convfac = me.getValue().abs().toTerm(numSort);
				rcomb.add(t.term(times, convfac, convme));
			} else if (me.getValue().equals(Rational.ONE)) {
				lcomb.add(convme);
			} else if (me.getValue().signum() > 0) {
				final Term convfac = me.getValue().toTerm(numSort);
				lcomb.add(t.term(times, convfac, convme));
			}
		}
		final InfinitNumber constant = isInt ? mConstant.ceil() : mConstant;
		if (!constant.mA.equals(Rational.ZERO)) {
			rcomb.add(constant.mA.negate().toTerm(numSort));
		}
		if (lcomb.isEmpty() && rcomb.isEmpty()) {
			// We either have 0<=0 or 0<0
			return constant.mEps == 0 ? t.mTrue : t.mFalse;
		}
		final FunctionSymbol plus = t.getFunction("+", binfunc);
		Term tlcomb, trcomb;
		switch (lcomb.size()) {
		case 0:
			tlcomb = Rational.ZERO.toTerm(numSort);
			break;
		case 1:
			tlcomb = lcomb.get(0);
			break;
		default:
			tlcomb = t.term(plus, lcomb.toArray(new Term[lcomb.size()]));
		}
		switch (rcomb.size()) {
		case 0:
			trcomb = Rational.ZERO.toTerm(numSort);
			break;
		case 1:
			trcomb = rcomb.get(0);
			break;
		default:
			trcomb = t.term(plus, rcomb.toArray(new Term[rcomb.size()]));
		}
		return t.term(constant.mEps == 0 ? "<=" : "<", tlcomb, trcomb);
	}

	@Override
	public int hashCode() {
		return mConstant.hashCode() + 1021 * mSummands.hashCode();
	}
}
