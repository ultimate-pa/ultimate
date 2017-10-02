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
package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.NonRecursive;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 *  Represents an affine term.  An affine term is a sum
 *  <pre>Σ c_i * x_i + c,</pre>
 *  where c_i, c are rational (or integer) constants
 *  and x_i are flat terms that are not themselves affine terms.
 *
 *  @author hoenicke.
 */
public final class SMTAffineTerm extends Term {

	private final Sort mSort;
	private final Map<Term, Rational> mSummands;
	private final Rational mConstant;

	private SMTAffineTerm(
	        final Map<Term, Rational> summands, final Rational constant, final Sort sort) {
		super(constant.hashCode() * 11 + summands.hashCode()
		        + 1423 * sort.hashCode());
		mSort = sort;
		mSummands = summands;
		mConstant = constant;
	}

	public static SMTAffineTerm create(
	        final Map<Term, Rational> summands, final Rational constant, final Sort sort) {
		return new SMTAffineTerm(summands, constant, sort);
	}

	public static SMTAffineTerm create(final Rational rat, final Sort sort) {
		return create(Collections.<Term,Rational>emptyMap(), rat, sort);
	}

	public static SMTAffineTerm create(final Term term) {
		if (term instanceof SMTAffineTerm) {
			return (SMTAffineTerm) term;
		}
		return create(Rational.ONE, term);
	}

	public static SMTAffineTerm create(final Rational factor, final Term subterm) {
		final Sort sort = subterm.getSort();
		Map<Term, Rational> summands;
		Rational constant;
		if (factor.equals(Rational.ZERO)) {
			summands = Collections.emptyMap();
			constant = Rational.ZERO;
		} else if (subterm instanceof SMTAffineTerm) {
			final SMTAffineTerm a = (SMTAffineTerm) subterm;
			constant = a.mConstant.mul(factor);
			summands = new HashMap<Term, Rational>();
			for (final Map.Entry<Term,Rational> me : a.mSummands.entrySet()) {
				summands.put(me.getKey(), me.getValue().mul(factor));
			}
		} else if (subterm instanceof ConstantTerm) {
			final Object value = ((ConstantTerm) subterm).getValue();
			if (value instanceof BigInteger) {
				constant = Rational.valueOf(
				        (BigInteger) value, BigInteger.ONE).mul(factor);
				summands = Collections.emptyMap();
			} else if (value instanceof BigDecimal) {
				final BigDecimal decimal = (BigDecimal) value;
				if (decimal.scale() <= 0) {
					final BigInteger num = decimal.toBigInteger();
					constant = Rational.valueOf(num, BigInteger.ONE).mul(factor);
				} else {
					final BigInteger num = decimal.unscaledValue();
					final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
					constant = Rational.valueOf(num, denom).mul(factor);
				}
				summands = Collections.emptyMap();
			} else if (value instanceof Rational) {
				constant = (Rational) value;
				summands = Collections.emptyMap();
			} else {
				summands = Collections.singletonMap(subterm, factor);
				constant = Rational.ZERO;
			}
		} else {
			summands = Collections.singletonMap(subterm, factor);
			constant = Rational.ZERO;
		}
		return create(summands, constant, sort);
	}

	public SMTAffineTerm add(final SMTAffineTerm a2) {
		assert getSort().equals(a2.getSort());
		return addUnchecked(a2, true);
	}

	public SMTAffineTerm addUnchecked(final SMTAffineTerm a2, final boolean sortCorrect) {
		final Map<Term, Rational> summands = new HashMap<Term, Rational>();
		summands.putAll(mSummands);
		for (final Map.Entry<Term,Rational> entry : a2.mSummands.entrySet()) {
			final Term var = entry.getKey();
			if (summands.containsKey(var)) {
				final Rational r = summands.get(var).add(entry.getValue());
				if (r.equals(Rational.ZERO)) {
					summands.remove(var);
				} else {
					summands.put(var, r);
				}
			} else {
				summands.put(var, entry.getValue());
			}
		}
		return create(summands, mConstant.add(a2.mConstant),
				sortCorrect ? mSort
					: a2.getSort().getName().equals("Real")
							? a2.getSort() : mSort);
	}

	/**
	 * Add a rational constant to this affine term.
	 * @param c the constant to add.
	 * @return the sum of this and the constant.
	 */
	public SMTAffineTerm add(final Rational c) {
		return create(mSummands, mConstant.add(c), mSort);
	}

	/**
	 * Convert affine term to a different sort.  This should only be used
	 * to convert from int to real, as it does not truncate.
	 * @param other  the affine term to convert.
	 * @param sort   the new sort.
	 */
	public SMTAffineTerm typecast(final Sort realSort) {
		return create(mSummands, mConstant, realSort);
	}

	/**
	 * Multiply a rational constant with this affine term.
	 * @param c the constant to multiply.
	 * @return the product of this and the constant.
	 */
	public SMTAffineTerm mul(final Rational factor) {
		if (factor.equals(Rational.ZERO)) {
			return create(Rational.ZERO, mSort);
		}

		final Rational constant = mConstant.mul(factor);
		final HashMap<Term, Rational> summands = new HashMap<Term, Rational>();
		for (final Map.Entry<Term,Rational> me : mSummands.entrySet()) {
			summands.put(me.getKey(), me.getValue().mul(factor));
		}
		return create(summands, constant, mSort);
	}
	public SMTAffineTerm div(final Rational c) {
		return mul(c.inverse());
	}
	public SMTAffineTerm negate() {
		return mul(Rational.MONE);
	}

	public boolean isConstant() {
		return mSummands.isEmpty();
	}
	public Rational getConstant() {
		return mConstant;
	}

	public boolean isIntegral() {
		return mSort.getName().equals("Int");
	}

	@Override
	public boolean equals(final Object o) { // NOCHECKSTYLE
		if (!(o instanceof SMTAffineTerm)) {
			return false;
		}
		final SMTAffineTerm l = (SMTAffineTerm) o;
		return mSort == l.mSort
			&& mConstant.equals(l.mConstant)
			&& mSummands.equals(l.mSummands);
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	Rational getCoefficient(final Term subterm) {
		final Rational coeff = mSummands.get(subterm);
		return coeff == null ? Rational.ZERO : coeff;
	}

	public Rational getGcd() {
		assert (!mSummands.isEmpty());
		final Iterator<Rational> it = mSummands.values().iterator();
		Rational gcd = it.next().abs();
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		return gcd;
	}

	public Map<Term, Rational> getSummands() {
		return mSummands;
	}

	/**
	 * Convert the affine term to plain SMTLib term.
	 * Note that this is does not convert terms inside this term.  Instead
	 * use the static method cleanup() for this, which works on arbitrary
	 * terms.
	 * @see SMTAffineTerm.cleanup
	 */
	private static Term toPlainTerm(
	        final Map<Term, Rational> summands, final Rational constant, final Sort sort) {
		assert sort.isNumericSort();
		final Theory t = sort.getTheory();
		int size = summands.size();
		if (size == 0 || !constant.equals(Rational.ZERO)) {
			size++;
		}
		final Term[] sum = new Term[size];
		int i = 0;
		for (final Map.Entry<Term,Rational> factor : summands.entrySet()) {
			Term convTerm = factor.getKey();
			if (!convTerm.getSort().equals(sort)) {
				convTerm = t.term("to_real", convTerm);
			}
			if (factor.getValue().equals(Rational.MONE)) {
				convTerm = t.term("-", convTerm);
			} else if (!factor.getValue().equals(Rational.ONE)) {
				final Term convfac = factor.getValue().toTerm(sort);
				convTerm = t.term("*", convfac, convTerm);
			}
			sum[i++] = convTerm;
		}
		if (i < size) {
			sum[i++] = constant.toTerm(sort);
		}
		return size == 1 ? sum[0] : t.term("+", sum);
	}

	@Override
	public void toStringHelper(final ArrayDeque<Object> m_Todo) {
		m_Todo.addLast(toPlainTerm(mSummands, mConstant, mSort));
	}

	@Override
	public String toString() {
		return cleanup(this).toString();
	}

	/**
	 * Remove all occurrences of SMTAffineTerm from the given term.
	 * @param term the term to clean up.
	 * @return an equivalent term without SMTAffineTerm classes.
	 */
	public static Term cleanup(final Term term) {
		return new TermTransformer() {
			@Override
			public void convert(final Term term) {
				if (term instanceof SMTAffineTerm) {
					final SMTAffineTerm affine = (SMTAffineTerm) term;
					enqueueWalker(new Walker() {
						@Override
						public void walk(final NonRecursive engine) {
							final HashMap<Term, Rational> summands =
							        new HashMap<Term, Rational>();
							for (final Rational v: affine.mSummands.values()) {
								summands.put(getConverted(), v);
							}
							final Term term = SMTAffineTerm.toPlainTerm(
							        summands, affine.mConstant, affine.mSort);
							setResult(term);
						}
					});
					for (final Term t : affine.mSummands.keySet()) {
						pushTerm(t);
					}
					return;
				}
				super.convert(term);
			}
		}.transform(term);
	}

	/**
	 * Normalize this term.  If this term corresponds to a singleton sum with
	 * coefficient 1 and constant 0, it will return the singleton term.
	 * Otherwise, it will return this.
	 * @param compiler TermCompiler used to unify SMTAffineTerms
	 * @return this or the singleton term corresponding to this.
	 */
	public Term normalize(final TermCompiler compiler) {
		if (mConstant.equals(Rational.ZERO) && mSummands.size() == 1) {
			final Map.Entry<Term, Rational> me =
					mSummands.entrySet().iterator().next();
			if (me.getValue().equals(Rational.ONE)
					// Fixes bug for to_real
					&& me.getKey().getSort() == mSort) {
				return me.getKey();
			}
		}
		return compiler.unify(this);
	}

	public Term internalize(final TermCompiler compiler) {
		SMTAffineTerm res = this;
		if (getTheory().getLogic().isIRA() && !isIntegral() && isAllInt()) {
			res = create(mSummands, mConstant, getTheory().getSort("Int"));
		}
		return res.normalize(compiler);
	}

	public boolean isAllIntSummands() {
		for (final Map.Entry<Term, Rational> me : mSummands.entrySet()) {
			if (!me.getKey().getSort().getName().equals("Int")) {
				return false;
			}
			if (!me.getValue().isIntegral()) {
				return false;
			}
		}
		return true;
	}

	private boolean isAllInt() {
		return isAllIntSummands() && mConstant.isIntegral();
	}
}
