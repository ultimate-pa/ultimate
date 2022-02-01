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
package de.uni_freiburg.informatik.ultimate.lassoranker.termination.rankingfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;


/**
 * Implementation of ordinal arithmetic for ranking functions.
 * 
 * Ordinals are stored in base-ω Cantor normal form:
 * <pre>n1*ω^α1 + ... nk*ω^αk</pre>
 * for ordinals α1 > ... > αk and
 * natural numbers n1, ..., nk.
 * 
 * Ordinals are immutable.
 * 
 * WARNING: this class is not part of functional code and has not been
 * properly debugged!
 * 
 * @author Jan Leike
 * @see http://www.volny.cz/behounek/logic/papers/ordcalc/index.html
 *
 */
public final class Ordinal implements Comparable<Ordinal> {
	
	/**
	 * Corresponds to one term of the form
	 * <pre>n*ω^α</pre>
	 * 
	 * Components are immutable.
	 */
	private class Component {
		final BigInteger base;
		final Ordinal exponent;
		
		Component(final BigInteger base, final Ordinal exponent) {
			assert(base.compareTo(BigInteger.ZERO) > 0);
			this.base = base;
			this.exponent = exponent;
		}
		
		@Override
		public String toString() {
			final StringBuilder sb = new StringBuilder();
			if (exponent.equals(ONE)) {
				sb.append("w");
			} else if (!exponent.isZero()) {
				final String s = exponent.toString();
				sb.append("w^");
				if (s.contains(" ")) {
					sb.append("(");
					sb.append(s);
					sb.append(")");
				} else {
					sb.append(s);
				}
			}
			if (exponent.isZero()) {
				sb.append(base);
			} else if (!base.equals(BigInteger.ONE)) {
				sb.append(" * ");
				sb.append(base);
			}
			return sb.toString();
		}
	}
	
	/**
	 * The ordinal 0.
	 */
	public static final Ordinal ZERO = new Ordinal(BigInteger.ZERO);
	
	/**
	 * The ordinal 1.
	 */
	public static final Ordinal ONE = new Ordinal(BigInteger.ONE);
	
	/**
	 * The first limit ordinal omega.
	 */
	public static final Ordinal OMEGA = new Ordinal(ONE);
	
	private final List<Component> mcomponents;
	
	public static Ordinal fromInteger(final BigInteger i) {
		if (!i.abs().equals(i)) {
			throw new IllegalArgumentException(
					"There are no negative ordinals.");
		} if (i.equals(BigInteger.ZERO)) {
			return ZERO;
		} if (i.equals(BigInteger.ONE)) {
			return ONE;
		}
		return new Ordinal(i);
	}
	
	/**
	 * Construct an ordinal from a non-negative integer
	 */
	private Ordinal(final BigInteger i) {
		assert(i.abs().equals(i)); // i is non-negative
		if (i.equals(BigInteger.ZERO)) {
			mcomponents = Collections.emptyList();
		} else {
			mcomponents = Collections.singletonList(new Component(i, ZERO));
		}
	}
	
	/**
	 * Construct an ordinal of the form ω^α
	 * @param exponent the exponent α
	 */
	private Ordinal(final Ordinal exponent) {
		mcomponents = Collections.singletonList(
				new Component(BigInteger.ONE, exponent));
	}
	
	/**
	 * Construct an ordinal from a component list
	 */
	private Ordinal(final List<Component> components) {
		mcomponents = Collections.unmodifiableList(components);
	}
	
	/**
	 * Compare two ordinals for equality
	 */
	@Override
	public boolean equals(final Object obj) {
		if (obj instanceof Ordinal) {
			final Ordinal o = (Ordinal) obj;
			return compareTo(o) == 0;
		}
		return false;
	}
	
	@Override
	public int compareTo(final Ordinal o) {
		if (o.isZero()) {
			if (isZero()) {
				return 0;
			} else {
				return 1;
			}
		}
		if (isZero()) {
			return -1;
		}
		for (int i = 0; i < mcomponents.size(); ++i) {
			final Component c = mcomponents.get(i);
			if (i >= o.mcomponents.size()) {
				return 1;
			}
			final Component co = o.mcomponents.get(i);
			int z = c.exponent.compareTo(co.exponent);
			if (z != 0) {
				return z;
			}
			z = c.base.compareTo(co.base);
			if (z != 0) {
				return z;
			}
		}
		if (mcomponents.size() < o.mcomponents.size()) {
			return -1;
		}
		return 0;
	}
	
	@Override
	public int hashCode() {
		return mcomponents.hashCode();
	}
	
	/**
	 * @return whether this ordinal is equal to 0
	 */
	public boolean isZero() {
		return mcomponents.isEmpty();
	}
	
	/**
	 * @return whether this is a finite ordinal (i.e., a natural number)
	 */
	public boolean isFinite() {
		return isZero() || (mcomponents.size() == 1
				&& mcomponents.get(0).exponent.isZero());
	}
	
	/**
	 * Cast to integer; returns null if the ordinal is not finite
	 * @return this in form of a integer
	 */
	public BigInteger toInteger() {
		if (!isFinite()) {
			return null;
		}
		if (isZero()) {
			return BigInteger.ZERO;
		}
		return mcomponents.get(mcomponents.size() - 1).base;
	}
	
	/**
	 * @return whether this is a limit ordinal
	 * (there is no ordinal β such that this is β + 1)
	 */
	public boolean isLimit() {
		if (mcomponents.isEmpty()) {
			return false;
		}
		final Component last = mcomponents.get(mcomponents.size() - 1);
		return !last.exponent.isZero();
	}
	
	/**
	 * Computes the sum of this with another ordinal
	 * Warning: this operation is *not* commutative.
	 */
	public Ordinal add(final Ordinal o) {
		/*
		 * Let
		 *    a = sum{i=1..k} omega^{ai} * ni,
		 *    b = sum{i=1..q} omega^{bi} * mi
		 * be ordinals in the Cantor normal form. Let r be the index such
		 * that ar = b1 (if the term with the exponent b1 is not present in
		 * the Cantor normal form of a, it should be added into its proper
		 * place with the zero coefficient nr). Then
		 *    sum{i=1..r-1} omega^{ai}*ni + omega^{b1}*(nr+m1)
		 *                                  + sum{j=2..q} omega^{bj}*mj
		 * is the Cantor normal form of a + b.
		 */
		if (isFinite() && o.isFinite()) {
			return new Ordinal(toInteger().add(o.toInteger()));
		}
		if (compareTo(o) < 0) {
			return o;
		}
		if (o.isZero()) {
			return this;
		}
		final List<Component> result = new ArrayList<Component>();
		final Ordinal oexp = o.mcomponents.get(0).exponent;
		Component last = null;
		for (final Component c : mcomponents) {
			if (c.exponent.compareTo(oexp) > 0) {
				result.add(c);
			} else {
				last = c;
				break;
			}
		}
		if (last != null && last.exponent.compareTo(oexp) == 0) {
			result.add(new Component(last.base.add(o.mcomponents.get(0).base),
					oexp));
			for (int i = 1; i < o.mcomponents.size(); ++i) {
				// omit first component (i = 1)
				result.add(o.mcomponents.get(i));
			}
		} else {
			result.addAll(o.mcomponents);
		}
		return new Ordinal(result);
	}
	
	/**
	 * Computes the product of this with another ordinal
	 * Warning: this operation is *not* commutative.
	 */
	public Ordinal mult(final Ordinal o) {
		/*
		 * Let
		 *    a = sum{i=1..k} omega^{ai}*ni,
		 *    b = sum{j=1..q-1} omega^{bj}*mj + m
		 * be ordinals in the Cantor normal form. Then the Cantor normal form
		 * of a * b is
		 *    sum{j=1..q-1} omega^{a1+bj}*mj + omega^{a1}*n1*m
		 *                                   + sum{i=2..k} omega^{ai}*ni
		 * if m > 0, or
		 *    sum{j=1..q-1} omega^{a1+bj}*mj
		 * if m = 0.
		 */
		if (isZero()) {
			return ZERO;
		}
		final List<Component> result = new ArrayList<Component>();
		final Component c = mcomponents.get(0);
		BigInteger last = null;
		for (final Component co : o.mcomponents) {
			if (co.exponent.isZero()) {
				last = co.base;
				break;
			}
			result.add(new Component(co.base, c.exponent.add(co.exponent)));
		}
		if (last != null) {
			// o is not a limit ordinal
			result.add(new Component(c.base.multiply(last), c.exponent));
			for (int i = 1; i < mcomponents.size(); ++i) {
				// omit first component (i = 1)
				result.add(mcomponents.get(i));
			}
		}
		return new Ordinal(result);
	}
	
	@Override
	public String toString() {
		if (isZero()) {
			return "0";
		}
		final StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (final Component c : mcomponents) {
			if (!first) {
				sb.append(" + ");
			}
			sb.append(c);
			first = false;
		}
		return sb.toString();
	}
	
	public static void testcases() {
		assert(!ONE.isZero());
		assert(ONE.isFinite());
		assert(!ZERO.equals(ONE));
		assert(OMEGA.isLimit());
		assert(!OMEGA.isFinite());
		assert(!OMEGA.isZero());
		assert(OMEGA.add(ZERO).equals(OMEGA));
		assert(!OMEGA.add(ONE).equals(OMEGA));
		assert(ONE.add(OMEGA).equals(OMEGA));
		assert(OMEGA.mult(ONE).equals(OMEGA));
		assert(!OMEGA.mult(OMEGA).equals(OMEGA));
	}
}
