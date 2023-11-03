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
package de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Represents a modifiable affin term, i.e. SUM_i c_i * x_i + c, where the x_i are initially nonbasic variable.
 *
 * @author hoenicke.
 */
public class MutableAffineTerm {
	TreeMap<LinVar, Rational> mSummands = new TreeMap<>();
	InfinitesimalNumber mConstant;

	public MutableAffineTerm() {
		mConstant = InfinitesimalNumber.ZERO;
	}

	public MutableAffineTerm add(final Rational c) {
		mConstant = mConstant.add(new InfinitesimalNumber(c, 0));
		return this;
	}

	public MutableAffineTerm add(final InfinitesimalNumber c) {
		mConstant = mConstant.add(c);
		return this;
	}

	public MutableAffineTerm add(final Rational c, final LinVar var) {
		if (c.equals(Rational.ZERO)) {
			return this;
		}
		if (var.isInitiallyBasic()) {
			for (final Map.Entry<LinVar, BigInteger> me : var.getLinTerm().entrySet()) {
				add(c.mul(me.getValue()), me.getKey());
			}
		} else {
			addSimple(c, var);
		}
		return this;
	}

	private void addMap(final Rational c, final Map<LinVar, Rational> linterm) {
		for (final Map.Entry<LinVar, Rational> summand : linterm.entrySet()) {
			addSimple(c.mul(summand.getValue()), summand.getKey());
		}
	}

	private void addSimple(Rational c, final LinVar term) {
		assert (!c.equals(Rational.ZERO));
		final Rational oldc = mSummands.remove(term);
		if (oldc != null) {
			c = oldc.add(c);
			if (c.equals(Rational.ZERO)) {
				return;
			}
		}
		mSummands.put(term, c);
	}

	public MutableAffineTerm add(final Rational c, final MutableAffineTerm a) {
		if (c != Rational.ZERO) {
			addMap(c, a.mSummands);
			mConstant = mConstant.add(a.mConstant.mul(c));
		}
		return this;
	}

	public MutableAffineTerm mul(final Rational c) {
		if (c.equals(Rational.ZERO)) {
			mSummands.clear();
		} else if (!c.equals(Rational.ONE)) {
			for (final Map.Entry<LinVar, Rational> summand : mSummands.entrySet()) {
				summand.setValue(c.mul(summand.getValue()));
			}
			mConstant = mConstant.mul(c);
		}
		return this;
	}

	public MutableAffineTerm div(final Rational c) {
		return mul(c.inverse());
	}

	public MutableAffineTerm negate() {
		return mul(Rational.MONE);
	}

	public boolean isConstant() {
		return mSummands.isEmpty();
	}

	public InfinitesimalNumber getConstant() {
		return mConstant;
	}

	public TreeMap<LinVar, Rational> getSummands() {
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
		for (final Entry<LinVar, Rational> entry : mSummands.entrySet()) {
			final LinVar var = entry.getKey();
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

	public Sort getSort(final Theory t) {
		return isInt() ? t.getSort("Int") : t.getSort("Real");
	}

	/**
	 * Convert the affine term to a term in our core theory.
	 * @param useAuxVars
	 *            use auxiliary variables for non-variable terms (unimplemented).
	 */
	public Term toSMTLib(final Theory t, final boolean isInt) {
		final Sort numSort = isInt ? t.getSort("Int") : t.getSort("Real");
		assert (numSort != null);
		final Sort[] binfunc = new Sort[] { numSort, numSort };
		final FunctionSymbol times = t.getFunction("*", binfunc);
		final FunctionSymbol plus = t.getFunction("+", binfunc);
		FunctionSymbol negate = t.getFunction("-", numSort);
		if (negate == null) {
			negate = t.getFunction("-", numSort);
		}
		assert (!isInt || mConstant.mReal.isIntegral());
		final Term constTerm = mConstant.mReal.equals(Rational.ZERO) ? null : mConstant.mReal.toTerm(numSort);
		final Term[] terms = new Term[mSummands.size() + (constTerm == null ? 0 : 1)];
		if (constTerm != null) {
			terms[mSummands.size()] = constTerm;
		}
		int offset = 0;
		for (final Map.Entry<LinVar, Rational> me : mSummands.entrySet()) {
			final LinVar lv = me.getKey();
			Term convme = lv.getTerm();
			// if affine term is integral it may only add integers.
			assert (!isInt || lv.isInt());
			assert (!isInt || me.getValue().isIntegral());
			if (!isInt && lv.isInt()) {
				final Sort intSort = t.getSort("Int");
				final FunctionSymbol toReal = t.getFunction("to_real", intSort);
				convme = t.term(toReal, convme);
			}
			if (!me.getValue().equals(Rational.ONE)) {
				final Term convfac = me.getValue().toTerm(numSort);
				convme = t.term(times, convfac, convme);
			}
			terms[offset++] = convme;
		}
		if (terms.length == 0) {
			return Rational.ZERO.toTerm(numSort);
		} else if (terms.length == 1) {
			return terms[0];
		} else {
			return t.term(plus, terms);
		}
	}

	public boolean isInt() {
		for (final LinVar v : mSummands.keySet()) {
			if (!v.isInt()) {
				return false;
			}
		}
		return true;
	}

	/**
	 * Create the SMTLib formula for the term <code>this <= 0</code>.
	 *
	 * @param smtTheory
	 *            Theory used in conversion.
	 * @return The SMTLib term representing the formula <code>this <= 0</code>.
	 */
	public Term toSMTLibLeq0(final Theory smtTheory) {
		assert mConstant.mEps >= 0;
		if (isConstant()) {
			return mConstant.compareTo(InfinitesimalNumber.ZERO) <= 0 ? smtTheory.mTrue : smtTheory.mFalse;
		}
		final boolean isInt = isInt();
		final Sort sort = smtTheory.getSort(isInt ? "Int" : "Real");
		final String comp = mConstant.mEps == 0 ? "<=" : "<";
		final Term zero = Rational.ZERO.toTerm(sort);
		return smtTheory.term(comp, toSMTLib(smtTheory, isInt), zero);
	}
}
