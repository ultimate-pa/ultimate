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
package de.uni_freiburg.informatik.ultimate.lassoranker;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * This represents an affine term in the form of
 * 
 * <pre>Σ c_i * x_i + c,</pre>
 * 
 * where c_i, c are rational constants
 * and x_i are variables.
 * 
 * This is very similar to the AffineTerm in RCFGBuilder, however, it does
 * not require a Sort object at construction time. Thus this object can be
 * constructed without a script instance.
 * 
 * @author Jan Leike
 */
public class AffineTerm implements Serializable {
	private static final long serialVersionUID = -4454719554662175493L;
	
	private Rational m_Constant;
	private final Map<Term, Rational> m_Coefficients;
	
	/**
	 * Construct the affine term 0
	 */
	public AffineTerm() {
		m_Coefficients = new LinkedHashMap<Term, Rational>();
		m_Constant = Rational.ZERO;
	}
	
	/**
	 * Copy constructor
	 */
	public AffineTerm(AffineTerm at) {
		m_Constant = at.m_Constant;
		m_Coefficients = new LinkedHashMap<Term, Rational>(at.m_Coefficients);
	}
	
	/**
	 * Construct an affine term from a constant
	 */
	public AffineTerm(BigInteger i) {
		this();
		m_Constant = Rational.valueOf(i, BigInteger.ONE);
	}
	
	/**
	 * Construct an affine term from a constant
	 */
	public AffineTerm(Rational r) {
		this();
		m_Constant = r;
	}
	
	/**
	 * Construct an affine term from a variable with coefficient
	 */
	public AffineTerm(Term var, Rational r) {
		this();
		m_Coefficients.put(var, r);
	}
	
	/**
	 * @return whether this is just a rational constant
	 */
	public boolean isConstant() {
		return m_Coefficients.isEmpty();
	}
	
	/**
	 * @return whether this is zero
	 */
	public boolean isZero() {
		return m_Coefficients.isEmpty() && m_Constant.equals(Rational.ZERO);
	}
	
	/**
	 * @return the affine constant c
	 */
	public Rational getConstant() {
		return m_Constant;
	}
	
	/**
	 * Add a rational to this
	 */
	public void add(Rational r) {
		m_Constant = m_Constant.add(r);
	}
	
	/**
	 * Add a variable-coefficient pair to this
	 */
	public void add(Term var, Rational c) {
		if (m_Coefficients.containsKey(var)) {
			Rational r = m_Coefficients.get(var).add(c);
			if (!r.equals(Rational.ZERO)) {
				m_Coefficients.put(var, r);
			} else {
				m_Coefficients.remove(var);
			}
		} else {
			if (!c.equals(Rational.ZERO)) {
				m_Coefficients.put(var, c);
			}
		}
	}
	
	/**
	 * Add another affine term to this.
	 */
	public void add(AffineTerm p) {
		this.add(p.m_Constant);
		for (Map.Entry<Term, Rational> entry : p.m_Coefficients.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * Multiply this with a Rational
	 */
	public void mult(Rational r) {
		m_Constant = m_Constant.mul(r);
		for (Term var : m_Coefficients.keySet()) {
			m_Coefficients.put(var, m_Coefficients.get(var).mul(r));
		}
	}
	
	/**
	 * @param script current SMT script
	 * @return this as a term of sort "Real"
	 */
	public Term asRealTerm(Script script) {
		Term[] summands = new Term[m_Coefficients.size() + 1];
		int i = 0;
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			Term coeff = entry.getValue().toTerm(script.sort("Real")); 
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		summands[i] = m_Constant.toTerm(script.sort("Real"));
		return SmtUtils.sum(script, script.sort("Real"), summands);
	}
	
	/**
	 * @param script current SMT script
	 * @return the affine term as a term of sort "Int"
	 */
	public Term asIntTerm(Script script) {
		Term[] summands = new Term[m_Coefficients.size() + 1];
		int i = 0;
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			assert entry.getValue().isIntegral();
			Term coeff = script.numeral(entry.getValue().numerator());
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		assert m_Constant.isIntegral();
		summands[i] = script.numeral(m_Constant.numerator());
		return SmtUtils.sum(script, script.sort("Int"), summands);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			if (entry.getValue().isNegative() || !first) {
				if (!first) {
					sb.append(" ");
				}
				sb.append(entry.getValue().isNegative() ? "- " : "+ ");
			}
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
			first = false;
		}
		if (!m_Constant.equals(Rational.ZERO) || sb.length() == 0) {
			if (m_Constant.isNegative() || !first) {
				if (!first) {
					sb.append(" ");
				}
				sb.append(m_Constant.isNegative() ? "- " : "+ ");
			}
			sb.append(m_Constant.abs());
		}
		return sb.toString();
	}
}