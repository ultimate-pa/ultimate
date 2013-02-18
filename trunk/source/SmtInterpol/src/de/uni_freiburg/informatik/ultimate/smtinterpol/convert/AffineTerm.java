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

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.cclosure.CCTerm;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.LinArSolve;
import de.uni_freiburg.informatik.ultimate.smtinterpol.theory.linar.MutableAffinTerm;


/**
 *  Represents an affine term.  An affine term is a sum
 *  <pre>Σ c_i * x_i + c,</pre>
 *  where c_i, c are rational (or integer) constants 
 *  and x_i are flat terms that are not themselves affine terms.
 *    
 *  @author hoenicke.
 */
public class AffineTerm extends FlatTerm {
	private final Sort m_sort;
	private final Map<FlatTerm, Rational> m_summands;
	private final Rational m_constant;
	SharedTermOld m_shared;
	
	public AffineTerm(ConvertFormula converter, Rational rat, Sort sort) {
		super(converter);
		m_summands = Collections.emptyMap();
		m_constant = rat;
		m_sort = sort;
	}
	
	public AffineTerm(FlatTerm flatTerm) {
		this(Rational.ONE, flatTerm);
	}

	public AffineTerm(Rational factor, FlatTerm subterm) {
		super(subterm.m_converter);
		m_sort = subterm.getSort();
		if (factor.equals(Rational.ZERO)) {
			m_summands = Collections.emptyMap();
			m_constant = Rational.ZERO;
		} else if (subterm instanceof AffineTerm) {
			AffineTerm a = (AffineTerm) subterm;
			this.m_constant = a.m_constant.mul(factor);
			this.m_summands = new HashMap<FlatTerm, Rational>();
			for (Map.Entry<FlatTerm,Rational> me : a.m_summands.entrySet()) {
				m_summands.put(me.getKey(), me.getValue().mul(factor));
			}
		} else {
			m_summands = Collections.singletonMap(subterm, factor);
			m_constant = Rational.ZERO;
		}
	}
	
	public AffineTerm(Rational factor, AffineTerm subterm) {
		super(subterm.m_converter);
		m_sort = subterm.getSort();
		if (factor.equals(Rational.ZERO)) {
			m_summands = Collections.emptyMap();
			m_constant = Rational.ZERO;
		} else {
			this.m_constant = subterm.m_constant.mul(factor);
			this.m_summands = new HashMap<FlatTerm, Rational>();
			for (Map.Entry<FlatTerm,Rational> me : subterm.m_summands.entrySet()) {
				m_summands.put(me.getKey(), me.getValue().mul(factor));
			}
		}
	}
	
	public AffineTerm(AffineTerm a1, AffineTerm a2) {
		super(a1.m_converter);
		assert (a1.m_sort == a2.m_sort && a1.m_converter == a2.m_converter);
		this.m_sort = a1.m_sort;
		this.m_constant = a1.m_constant.add(a2.m_constant);
		this.m_summands = new HashMap<FlatTerm, Rational>();
		this.m_summands.putAll(a1.m_summands);
		for (FlatTerm var : a2.m_summands.keySet()) {
			if (m_summands.containsKey(var)) {
				Rational r = m_summands.get(var).add(a2.m_summands.get(var));
				if (r.equals(Rational.ZERO))
					m_summands.remove(var);
				else {
					m_summands.put(var, r);
				}
			} else {
				m_summands.put(var, a2.m_summands.get(var));
			}
		}
	}

	/**
	 * Create an affine term for the sum of other and offset. 
	 * @param other  the affine term to add to.
	 * @param offset the constant to add.
	 */
	public AffineTerm(AffineTerm other, Rational offset) {
		super(other.m_converter);
		m_summands = other.m_summands;
		m_constant = other.m_constant.add(offset);
		m_sort = other.m_sort;
	}
	
	/**
	 * Convert affine term to a different sort.  This should only be used 
	 * to convert from int to real, as it does not truncate.
	 * @param other  the affine term to convert.
	 * @param sort   the new sort.
	 */
	public AffineTerm(AffineTerm other, Sort sort) {
		super(other.m_converter);
		m_summands = other.m_summands;
		m_constant = other.m_constant;
		m_sort = sort;
	}
	
	public AffineTerm add(AffineTerm l) {
		return new AffineTerm(this, l);
	}
	
	/**
	 * Add a rational constant to this affine term. 
	 * @param c the constant to add.
	 * @return the sum of this and the constant.
	 */
	public AffineTerm add(Rational c) {
		return new AffineTerm(this, c);
	}
	
	/**
	 * Multiply a rational constant with this affine term. 
	 * @param c the constant to multiply.
	 * @return the product of this and the constant.
	 */
	public AffineTerm mul(Rational c) {
		return c.equals(Rational.ONE) ? this : new AffineTerm(c, this);
	}
	public AffineTerm div(Rational c) {
		return mul(Rational.ONE.div(c));
	}
	public AffineTerm negate() {
		return mul(Rational.MONE);
	}

	public boolean isConstant() {
		return m_summands.isEmpty();
	}
	public Rational getConstant() {
		return m_constant;
	}
	
	public boolean isIntegral() {
		return m_sort.getName().equals("Int");
	}
	
	public int hashCode() {
		return m_constant.hashCode()*11 + m_summands.hashCode();
	}
	
	public boolean equals(Object o) {
		if (!(o instanceof AffineTerm))
			return false;
		AffineTerm l = (AffineTerm) o;
		return m_sort == l.m_sort 
			&& m_constant.equals(l.m_constant)
			&& m_summands.equals(l.m_summands);
	}
	
	public void toStringHelper(StringBuilder sb, HashSet<FlatTerm> visited) {
		boolean isFirst = true;
		for (Entry<FlatTerm,Rational> entry : m_summands.entrySet()) {
			FlatTerm var = entry.getKey();
			Rational fact = entry.getValue();
			if (fact.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			fact = fact.abs();
			if (!fact.equals(Rational.ONE))
				sb.append(fact).append("*");
			var.toStringHelper(sb, visited);
			isFirst = false;
		}
		if (m_constant.equals(Rational.ZERO)) {
			if (isFirst)
				sb.append("0");
		} else {
			if (m_constant.isNegative()) {
				sb.append(isFirst ? "-" : " - ");
			} else {
				sb.append(isFirst ? "" : " + ");
			}
			sb.append(m_constant.abs());
		}
	}
	
	/**
	 * Convert a rational constant to a term of the correct sort.
	 * @param c the constant to convert.
	 * @return an smt term representing constant c.
	 */
	final Term convertConstant(Rational c) {
		return isIntegral() ? m_converter.getTheory().numeral(c.numerator())
			: m_converter.getTheory().rational(c.numerator(), c.denominator());
	}
	
	/**
	 * Convert the affine term to SMT lib
	 * 
	 */ 
	@Override
	public Term getSMTTerm(boolean useAuxVars) {
		Theory t = m_converter.getTheory();
		Sort[] binfunc = new Sort[] {m_sort,m_sort};
		FunctionSymbol times = t.getFunction("*", binfunc);
		FunctionSymbol plus = t.getFunction("+", binfunc);
		FunctionSymbol negate = t.getFunction("-", m_sort);
		if (negate == null)
			negate = t.getFunction("-", m_sort);

		int size = m_summands.size();
		if (size == 0 || !m_constant.equals(Rational.ZERO))
			size++;
		Term[] sum = new Term[size];
		int i = 0;
		for (Map.Entry<FlatTerm,Rational> factor : m_summands.entrySet()) {
			Term convTerm = (Term) factor.getKey().getSMTTerm(useAuxVars);
			if (!convTerm.getSort().equals(m_sort)) {
				FunctionSymbol toreal = 
					t.getFunction("to_real", convTerm.getSort()); 
				convTerm = t.term(toreal, convTerm);
			}
			if (factor.getValue().equals(Rational.MONE)) {
				convTerm = t.term(negate, convTerm);
			} else if (!factor.getValue().equals(Rational.ONE)) {
				Term convfac = convertConstant(factor.getValue());
				convTerm = t.term(times, convfac, convTerm);
			}
			sum[i++] = convTerm;
		}
		if (i < size) {
			sum[i++] = convertConstant(m_constant);
		}
		return size == 1 ? sum[0] : t.term(plus, sum);
	}
	
	@Override
	public Sort getSort() {
		return m_sort;
	}

	@Override
	public SharedTermOld toShared() {
		if (m_shared != null) {
			// m_shared.getOffset() == null means we removed this shared term
			if (m_shared.getOffset() != null)
				return m_shared;
		}
		if (m_constant.equals(Rational.ZERO) && m_summands.size() == 1
			&& m_summands.values().iterator().next().equals(Rational.ONE)) {
			m_shared = m_summands.keySet().iterator().next().toShared();
		} else {
			m_shared = m_converter.createSharedAffineTerm(this);
		}
		return m_shared;
	}
	
	@Override
	public AffineTerm toAffineTerm() {
		return this;
	}
	
	@Override
	public CCTerm toCCTerm() {
		// Ugly: We need to intern the shared term
//		toShared().intern();
		return toShared().toCCTerm();
	}
	
	public MutableAffinTerm getMutableAffinTerm() {
		MutableAffinTerm mutTerm = new MutableAffinTerm();
		mutTerm.add(m_constant);
		for (Map.Entry<FlatTerm,Rational> summand : m_summands.entrySet()) {
			SharedTermOld shared = summand.getKey().toShared();
			Rational coeff = summand.getValue();
			shared.shareWithLinAr();
			if (shared.m_linvar != null)
//				mutTerm.add(shared.m_factor.mul(coeff), shared);
			mutTerm.add(shared.m_offset.mul(coeff));
		}
		return mutTerm;
	}

	Rational getCoefficient(FlatTerm subterm) {
		Rational coeff = m_summands.get(subterm);
		return coeff == null ? Rational.ZERO : coeff;
	}

	public Rational getGcd() {
		assert (!m_summands.isEmpty());
		Iterator<Rational> it = m_summands.values().iterator();
		Rational gcd = it.next().abs(); 
		while (it.hasNext()) {
			gcd = gcd.gcd(it.next().abs());
		}
		return gcd;
	}
	
	Rational getValue(LinArSolve linar) {
		return getMutableAffinTerm().getValue(linar);
	}

	public Map<FlatTerm, Rational> getSummands() {
		return m_summands;
	}
	public void accept(FlatTermVisitor visitor) {
		visitor.visit(this);
	}
}
