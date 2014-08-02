/*
 * Copyright (C) 2012-2014 University of Freiburg
 *
 * This file is part of the ULTIMATE LassoRanker Library.
 *
 * The ULTIMATE LassoRanker Library is free software: you can redistribute it
 * and/or modify it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * The ULTIMATE LassoRanker Library is distributed in the hope that it will
 * be useful, but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE LassoRanker Library. If not,
 * see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE LassoRanker Library, or any covered work, by
 * linking or combining it with Eclipse RCP (or a modified version of
 * Eclipse RCP), containing parts covered by the terms of the Eclipse Public
 * License, the licensors of the ULTIMATE LassoRanker Library grant you
 * additional permission to convey the resulting work.
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
public class Ordinal implements Comparable<Ordinal> {
	
	/**
	 * Corresponds to one term of the form
	 * <pre>n*ω^α</pre>
	 * 
	 * Components are immutable.
	 */
	private class Component {
		final BigInteger base;
		final Ordinal exponent;
		
		Component(BigInteger base, Ordinal exponent) {
			assert(base.compareTo(BigInteger.ZERO) > 0);
			this.base = base;
			this.exponent = exponent;
		}
		
		@Override
		public String toString() {
			StringBuilder sb = new StringBuilder();
			if (exponent.equals(ONE)) {
				sb.append("w");
			} else if (!exponent.isZero()) {
				String s = exponent.toString();
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
	
	private final List<Component> m_components;
	
	public static Ordinal fromInteger(BigInteger i) {
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
	private Ordinal(BigInteger i) {
		assert(i.abs().equals(i)); // i is non-negative
		if (i.equals(BigInteger.ZERO)) {
			m_components = Collections.emptyList();
		} else {
			m_components = Collections.singletonList(new Component(i, ZERO));
		}
	}
	
	/**
	 * Construct an ordinal of the form ω^α
	 * @param exponent the exponent α
	 */
	private Ordinal(Ordinal exponent) {
		m_components = Collections.singletonList(
				new Component(BigInteger.ONE, exponent));
	}
	
	/**
	 * Construct an ordinal from a component list
	 */
	private Ordinal(List<Component> components) {
		m_components = Collections.unmodifiableList(components);
	}
	
	/**
	 * Compare two ordinals for equality
	 */
	public boolean equals(Object obj) {
		if (obj instanceof Ordinal) {
			Ordinal o = (Ordinal) obj;
			return this.compareTo(o) == 0;
		}
		return false;
	}
	
	@Override
	public int compareTo(Ordinal o) {
		if (o.isZero()) {
			if (this.isZero()) {
				return 0;
			} else {
				return 1;
			}
		}
		if (this.isZero()) {
			return -1;
		}
		for (int i = 0; i < m_components.size(); ++i) {
			Component c = m_components.get(i);
			if (i >= o.m_components.size()) {
				return 1;
			}
			Component co = o.m_components.get(i);
			int z = c.exponent.compareTo(co.exponent);
			if (z != 0) {
				return z;
			}
			z = c.base.compareTo(co.base);
			if (z != 0) {
				return z;
			}
		}
		if (m_components.size() < o.m_components.size()) {
			return -1;
		}
		return 0;
	}
	
	@Override
	public int hashCode() {
		return m_components.hashCode();
	}
	
	/**
	 * @return whether this ordinal is equal to 0
	 */
	public boolean isZero() {
		return m_components.isEmpty();
	}
	
	/**
	 * @return whether this is a finite ordinal (i.e., a natural number)
	 */
	public boolean isFinite() {
		return isZero() || (m_components.size() == 1
				&& m_components.get(0).exponent.isZero());
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
		return m_components.get(m_components.size() - 1).base;
	}
	
	/**
	 * @return whether this is a limit ordinal
	 * (there is no ordinal β such that this is β + 1)
	 */
	public boolean isLimit() {
		if (m_components.isEmpty()) {
			return false;
		}
		Component last = m_components.get(m_components.size() - 1);
		return !last.exponent.isZero();
	}
	
	/**
	 * Computes the sum of this with another ordinal
	 * Warning: this operation is *not* commutative.
	 */
	public Ordinal add(Ordinal o) {
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
		if (this.isFinite() && o.isFinite()) {
			return new Ordinal(toInteger().add(o.toInteger()));
		}
		if (this.compareTo(o) < 0) {
			return o;
		}
		if (o.isZero()) {
			return this;
		}
		List<Component> result = new ArrayList<Component>();
		Ordinal oexp = o.m_components.get(0).exponent;
		Component last = null;
		for (Component c : m_components) {
			if (c.exponent.compareTo(oexp) > 0) {
				result.add(c);
			} else {
				last = c;
				break;
			}
		}
		if (last != null && last.exponent.compareTo(oexp) == 0) {
			result.add(new Component(last.base.add(o.m_components.get(0).base),
					oexp));
			for (int i = 1; i < o.m_components.size(); ++i) {
				// omit first component (i = 1)
				result.add(o.m_components.get(i));
			}
		} else {
			result.addAll(o.m_components);
		}
		return new Ordinal(result);
	}
	
	/**
	 * Computes the product of this with another ordinal
	 * Warning: this operation is *not* commutative.
	 */
	public Ordinal mult(Ordinal o) {
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
		List<Component> result = new ArrayList<Component>();
		Component c = m_components.get(0);
		BigInteger last = null;
		for (Component co : o.m_components) {
			if (co.exponent.isZero()) {
				last = co.base;
				break;
			}
			result.add(new Component(co.base, c.exponent.add(co.exponent)));
		}
		if (last != null) {
			// o is not a limit ordinal
			result.add(new Component(c.base.multiply(last), c.exponent));
			for (int i = 1; i < m_components.size(); ++i) {
				// omit first component (i = 1)
				result.add(m_components.get(i));
			}
		}
		return new Ordinal(result);
	}
	
	@Override
	public String toString() {
		if (isZero()) {
			return "0";
		}
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (Component c : m_components) {
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