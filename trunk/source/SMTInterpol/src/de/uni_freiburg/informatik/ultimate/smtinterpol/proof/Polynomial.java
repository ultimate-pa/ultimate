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

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.ConstantTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;

/**
 * Represents a polynomial. A polynomial is a sum
 *
 * <pre>
 * Σ c_i * x_i,
 * </pre>
 *
 * where c_i are rational (or integer) constants and x_i is a monomial, i.e. a product of a multiset of terms.
 *
 * @author Jochen Hoenicke
 */
public final class Polynomial {

	/**
	 * A polynomial is represented as a map from monomials to rational coefficients, where each monomial
	 * is represented by a map from term to the power of the term.  All coefficients must be non-zero and
	 * all powers must be positive.
	 */
	private final Map<Map<Term,Integer>, Rational> mSummands;

	public Polynomial() {
		mSummands = new LinkedHashMap<>();
	}

	public Polynomial(final Term term) {
		this();
		Term[] subterms;
		if (term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("+")) {
			subterms = ((ApplicationTerm) term).getParameters();
		} else {
			subterms = new Term[] { term };
		}
		for (final Term subterm : subterms) {
			Rational coefficient = Rational.ONE;
			Term[] factors;
			if (subterm instanceof ApplicationTerm && ((ApplicationTerm) subterm).getFunction().getName() == "*") {
				factors = ((ApplicationTerm) subterm).getParameters();
			} else {
				factors = new Term[]  { subterm };
			}
			Map<Term, Integer> monomial = new LinkedHashMap<>();
			for (Term f : factors) {
				final Rational constant = parseConstant(f);
				if (constant != null) {
					coefficient = coefficient.mul(constant);
				} else {
					if (f instanceof ApplicationTerm
							&& ((ApplicationTerm) f).getFunction().getName() == "to_real") {
						f = ((ApplicationTerm) f).getParameters()[0];
					}
					final Integer old = monomial.get(f);
					monomial.put(f,  old == null ? 1 : old + 1);
				}
			}
			if (monomial.isEmpty()) {
				monomial = Collections.emptyMap();
			} else if (monomial.size() == 1) {
				final Map.Entry<Term, Integer> entry = monomial.entrySet().iterator().next();
				monomial = Collections.singletonMap(entry.getKey(), entry.getValue());
			}
			final Rational old = mSummands.get(monomial);
			mSummands.put(monomial, old == null ? coefficient : old.add(coefficient));
		}
	}

	public static boolean isToReal(final Term term) {
		return term instanceof ApplicationTerm && ((ApplicationTerm) term).getFunction().getName().equals("to_real");
	}

	private static Rational convertConstantTerm(final ConstantTerm term) {
		Rational constant;
		final Object value = term.getValue();
		if (value instanceof BigInteger) {
			constant = Rational.valueOf((BigInteger) value, BigInteger.ONE);
		} else if (value instanceof BigDecimal) {
			final BigDecimal decimal = (BigDecimal) value;
			if (decimal.scale() <= 0) {
				final BigInteger num = decimal.toBigInteger();
				constant = Rational.valueOf(num, BigInteger.ONE);
			} else {
				final BigInteger num = decimal.unscaledValue();
				final BigInteger denom = BigInteger.TEN.pow(decimal.scale());
				constant = Rational.valueOf(num, denom);
			}
		} else if (value instanceof Rational) {
			constant = (Rational) value;
		} else {
			return null;
		}
		return constant;
	}

	private static Rational parseConstantWithoutFraction(Term term) {
		boolean isNegated = false;
		if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getFunction().getName().equals("-")
				&& ((ApplicationTerm) term).getParameters().length == 1) {
			term = ((ApplicationTerm) term).getParameters()[0];
			isNegated = true;
		}
		if (isToReal(term)) {
			term = ((ApplicationTerm) term).getParameters()[0];
		}
		if (term instanceof ConstantTerm) {
			Rational value = convertConstantTerm((ConstantTerm) term);
			if (isNegated && value != null) {
				value = value.negate();
			}
			return value;
		}
		return null;
	}

	/**
	 * Parse a term representing a constant number. This can be either a constant
	 * term, but it also accepts slightly non-standard representations of numbers.
	 *
	 * @param term the term to parse.
	 * @return the constant or null if the term is not a number.
	 */
	public static Rational parseConstant(final Term term) {
		if (term instanceof ApplicationTerm
				&& ((ApplicationTerm) term).getFunction().getName().equals("/")) {
			final Term[] params = ((ApplicationTerm) term).getParameters();
			final Rational numerator = parseConstantWithoutFraction(params[0]);
			final Rational denominator = parseConstantWithoutFraction(params[1]);
			if (numerator == null || denominator == null || denominator.signum() <= 0
					|| !numerator.isIntegral() || !denominator.isIntegral()) {
				return null;
			}
			return numerator.div(denominator);
		}
		return parseConstantWithoutFraction(term);
	}

	public void mul(final Rational factor) {
		if (factor == Rational.ZERO) {
			mSummands.clear();
			return;
		}

		for (final Map.Entry<Map<Term, Integer>, Rational> entry : mSummands.entrySet()) {
			entry.setValue(entry.getValue().mul(factor));
		}
	}

	public Map<Term, Integer> mulMonomials(final Map<Term, Integer> monom1, final Map<Term, Integer> monom2) {
		final Map<Term, Integer> result = new LinkedHashMap<>();
		result.putAll(monom1);
		for (final Map.Entry<Term, Integer> entry : monom2.entrySet()) {
			final Integer old = result.get(entry.getKey());
			result.put(entry.getKey(), old == null ? entry.getValue() : old + entry.getValue());
		}
		return result;
	}

	public void mul(final Polynomial other) {
		if (other.isConstant()) {
			mul(other.getConstant());
			return;
		}
		if (isConstant()) {
			final Rational constant = getConstant();
			mSummands.clear();
			add(constant, other);
			return;
		}
		final Polynomial newPolynomial = new Polynomial();
		for (final Map.Entry<Map<Term, Integer>,Rational> term1 : other.mSummands.entrySet()) {
			for (final Map.Entry<Map<Term, Integer>,Rational> term2 : mSummands.entrySet()) {
				final Map<Term, Integer> newMonomial = mulMonomials(term1.getKey(), term2.getKey());
				newPolynomial.add(term1.getValue().mul(term2.getValue()), newMonomial);
			}
		}
		mSummands.clear();
		mSummands.putAll(newPolynomial.mSummands);
	}

	public void add(final Rational factor, final Map<Term,Integer> monomial) {
		final Rational oldCoeff = mSummands.get(monomial);
		final Rational newCoeff = oldCoeff == null ? factor : oldCoeff.add(factor);
		if (newCoeff == Rational.ZERO) {
			mSummands.remove(monomial);
		} else {
			mSummands.put(monomial, newCoeff);
		}
	}

	public void add(final Rational constant) {
		add(constant, Collections.emptyMap());
	}

	public void add(final Rational factor, final Polynomial other) {
		for (final Map.Entry<Map<Term, Integer>, Rational> entry : other.mSummands.entrySet()) {
			add(factor.mul(entry.getValue()), entry.getKey());
		}
	}

	public void add(final Rational factor, final Term other) {
		add(factor, new Polynomial(other));
	}

	public boolean isConstant() {
		return mSummands.isEmpty()
				|| (mSummands.size() == 1 && mSummands.keySet().iterator().next().isEmpty());
	}

	public Rational getConstant() {
		final Rational coeff = mSummands.get(Collections.emptyMap());
		return coeff == null ? Rational.ZERO : coeff;
	}

	public boolean isZero() {
		return mSummands.isEmpty();
	}

	public Rational getGcd() {
		Rational gcd = Rational.ZERO;
		for (final Map.Entry<Map<Term, Integer>, Rational> term : mSummands.entrySet()) {
			if (!term.getKey().isEmpty()) {
				gcd = gcd.gcd(term.getValue().abs());
			}
		}
		return gcd;
	}

	public Map<Map<Term,Integer>, Rational> getSummands() {
		return mSummands;
	}

	/**
	 * Convert this polynomial to a plain SMTLib term. This function does not unify the terms.
	 *
	 * @param sort
	 *            the expected sort
	 */
	public Term toTerm(final Sort sort) {
		assert sort.isNumericSort();
		if (mSummands.isEmpty()) {
			return Rational.ZERO.toTerm(sort);
		}

		final Theory t = sort.getTheory();
		final int size = mSummands.size();
		final Term[] sum = new Term[size];
		int i = 0;
		for (final Map.Entry<Map<Term, Integer>, Rational> term : mSummands.entrySet()) {
			final Map<Term, Integer> monomial = term.getKey();
			final ArrayList<Term> factors = new ArrayList<>();
			factors.add(term.getValue().toTerm(sort));
			for (final Map.Entry<Term, Integer> f : monomial.entrySet()) {
				final int power = f.getValue();
				assert power > 0;
				for (int j = 0; j < power; j++) {
					factors.add(f.getKey());
				}
			}
			if (factors.size() == 1) {
				sum[i++] = factors.get(0);
			} else {
				sum[i++] = t.term(SMTLIBConstants.MUL, factors.toArray(new Term[factors.size()]));
			}
		}
		return size == 1 ? sum[0] : t.term("+", sum);
	}

	@Override
	/**
	 * Return a string representation of this SMTAffineTerm for debugging purposes.
	 */
	public String toString() {
		if (mSummands.isEmpty()) {
			return "0";
		}
		final StringBuilder sb = new StringBuilder();
		String comma = "";
		for (final Map.Entry<Map<Term, Integer>, Rational> monomial: mSummands.entrySet()) {
			sb.append(comma);
			sb.append(monomial.getValue());
			for (final Map.Entry<Term, Integer> entry : monomial.getKey().entrySet()) {
				final int power = entry.getValue();
				assert power > 0;
				final String repr = " * " + entry.getKey();
				for (int i = 0; i < entry.getValue(); i++) {
					sb.append(repr);
				}
			}
			comma = " + ";
		}
		return sb.toString();
	}

	public boolean isAllIntSummands() {
		for (final Map<Term,Integer> monomial : mSummands.keySet()) {
			for (final Term t : monomial.keySet()) {
				if (!t.getSort().getName().equals("Int")) {
					return false;
				}
			}
		}
		return true;
	}

	@Override
	public boolean equals(final Object other) {
		if (!(other instanceof Polynomial)) {
			return false;
		}
		final Polynomial o = (Polynomial) other;
		return mSummands.equals(o.mSummands);
	}

	@Override
	public int hashCode() {
		return mSummands.hashCode();
	}
}
