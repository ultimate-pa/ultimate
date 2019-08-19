/*
 * Copyright (C) 2014-2015 Jan Leike (leike@informatik.uni-freiburg.de)
 * Copyright (C) 2012-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE LassoRanker Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.SmtUtils;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * This represents an affine term in the form of
 *
 * <pre>
 * Σ c_i * x_i + c,
 * </pre>
 *
 * where c_i, c are rational constants and x_i are variables.
 *
 * This is very similar to the AffineTerm in RCFGBuilder, however, it does not require a Sort object at construction
 * time. Thus this object can be constructed without a script instance.
 *
 * @author Jan Leike
 */
public class AffineTerm implements Serializable {
	private static final long serialVersionUID = -4454719554662175493L;

	private Rational mConstant;
	private final Map<Term, Rational> mCoefficients;

	/**
	 * Construct the affine term 0
	 */
	public AffineTerm() {
		mCoefficients = new LinkedHashMap<>();
		mConstant = Rational.ZERO;
	}

	/**
	 * Copy constructor
	 */
	public AffineTerm(final AffineTerm at) {
		mConstant = at.mConstant;
		mCoefficients = new LinkedHashMap<>(at.mCoefficients);
	}

	/**
	 * Construct an affine term from a constant
	 */
	public AffineTerm(final BigInteger i) {
		this();
		mConstant = Rational.valueOf(i, BigInteger.ONE);
	}

	/**
	 * Construct an affine term from a constant
	 */
	public AffineTerm(final Rational r) {
		this();
		mConstant = r;
	}

	/**
	 * Construct an affine term from a variable with coefficient
	 */
	public AffineTerm(final Term var, final Rational r) {
		this();
		mCoefficients.put(var, r);
	}

	/**
	 * @return whether this is just a rational constant
	 */
	public boolean isConstant() {
		return mCoefficients.isEmpty();
	}

	/**
	 * @return whether this is zero
	 */
	public boolean isZero() {
		return mCoefficients.isEmpty() && mConstant.equals(Rational.ZERO);
	}

	/**
	 * @return the affine constant c
	 */
	public Rational getConstant() {
		return mConstant;
	}

	/**
	 * Add a rational to this
	 */
	public void add(final Rational r) {
		mConstant = mConstant.add(r);
	}

	/**
	 * Add a variable-coefficient pair to this
	 */
	public void add(final Term var, final Rational c) {
		if (mCoefficients.containsKey(var)) {
			final Rational r = mCoefficients.get(var).add(c);
			if (!r.equals(Rational.ZERO)) {
				mCoefficients.put(var, r);
			} else {
				mCoefficients.remove(var);
			}
		} else {
			if (!c.equals(Rational.ZERO)) {
				mCoefficients.put(var, c);
			}
		}
	}

	/**
	 * Add another affine term to this.
	 */
	public void add(final AffineTerm p) {
		this.add(p.mConstant);
		for (final Map.Entry<Term, Rational> entry : p.mCoefficients.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * Multiply this with a Rational
	 */
	public void mult(final Rational r) {
		mConstant = mConstant.mul(r);
		for (final Entry<Term, Rational> var : mCoefficients.entrySet()) {
			mCoefficients.put(var.getKey(), var.getValue().mul(r));
		}
	}

	/**
	 * @param script
	 *            current SMT script
	 * @return this as a term of sort "Real"
	 */
	public Term asRealTerm(final Script script) {
		final Term[] summands = new Term[mCoefficients.size() + 1];
		int i = 0;
		for (final Map.Entry<Term, Rational> entry : mCoefficients.entrySet()) {
			final Term coeff = entry.getValue().toTerm(SmtSortUtils.getRealSort(script));
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		summands[i] = mConstant.toTerm(SmtSortUtils.getRealSort(script));
		return SmtUtils.sum(script, SmtSortUtils.getRealSort(script), summands);
	}

	/**
	 * @param script
	 *            current SMT script
	 * @return the affine term as a term of sort "Int"
	 */
	public Term asIntTerm(final Script script) {
		final Term[] summands = new Term[mCoefficients.size() + 1];
		int i = 0;
		for (final Map.Entry<Term, Rational> entry : mCoefficients.entrySet()) {
			assert entry.getValue().isIntegral();
			final Term coeff = SmtUtils.constructIntValue(script, entry.getValue().numerator());
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		assert mConstant.isIntegral();
		summands[i] = SmtUtils.constructIntValue(script, mConstant.numerator());
		return SmtUtils.sum(script, SmtSortUtils.getIntSort(script), summands);
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (final Map.Entry<Term, Rational> entry : mCoefficients.entrySet()) {
			if (entry.getValue().isNegative() || !first) {
				if (!first) {
					sb.append(" ");
				}
				sb.append(entry.getValue().isNegative() ? "- " : "+ ");
			}
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
			first = false;
		}
		if (!mConstant.equals(Rational.ZERO) || sb.length() == 0) {
			if (mConstant.isNegative() || !first) {
				if (!first) {
					sb.append(" ");
				}
				sb.append(mConstant.isNegative() ? "- " : "+ ");
			}
			sb.append(mConstant.abs());
		}
		return sb.toString();
	}
}
