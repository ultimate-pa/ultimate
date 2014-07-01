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
package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Term2Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.SmtUtils;


/**
 * Represents an affine-linear function of the from
 * <pre>f(x) = Σ c_i * x_i + b</pre>
 * with a vector c_1, ... c_n and a constant b.
 * 
 * This is similar to the class LinearInequality, but serves a different
 * purpose.  The coefficients are restricted to integers and the variables
 * are Boogie variables.
 * 
 * This will be generated and administered by the AffineFunctionGenerator
 * class.  It generates parameters whose solution gives rise to this affine
 * function instance.
 * 
 * The purpose of this class is to serve as a foundation to ranking functions
 * and supporting invariants.
 * 
 * @author Jan Leike
 */
public class AffineFunction implements Serializable {
	private static final long serialVersionUID = -3142354398708751882L;
	
	protected final Map<RankVar, BigInteger> m_coefficients;
	protected BigInteger m_constant;
	
	public AffineFunction() {
		m_coefficients = new LinkedHashMap<RankVar, BigInteger>();
		m_constant = BigInteger.ZERO;
	}
	
	/**
	 * @return whether this function is a constant function
	 */
	public boolean isConstant() {
		return m_coefficients.isEmpty();
	}
	
	/**
	 * @return the constant
	 */
	public BigInteger getConstant() {
		return m_constant;
	}
	
	/**
	 * @param c set the constant to c
	 */
	public void setConstant(BigInteger c) {
		m_constant = c;
	}
	
	/**
	 * @return the set of RankVar's that occur in this function
	 */
	public Set<RankVar> getVariables() {
		return m_coefficients.keySet();
	}
	
//	/**
//	 * @return the set of (associated) BoogieVar's that occur in this function
//	 */
//	public Set<BoogieVar> getBoogieVariables() {
//		Set<BoogieVar> result = new LinkedHashSet<BoogieVar>();
//		for (RankVar rkVar : m_coefficients.keySet()) {
//			BoogieVar boogieVar = rkVar.getAssociatedBoogieVar();
//			if (boogieVar != null) {
//				result.add(boogieVar);
//			}
//		}
//		return result;
//	}
	
	/**
	 * @param var a Boogie variable
	 * @return the coefficient of to this variable
	 */
	public BigInteger get(BoogieVar var) {
		return m_coefficients.get(var);
	}
	
	/**
	 * Set the coefficient to a variable
	 * @param var a Boogie variable
	 * @param coeff the coefficient of this variable
	 */
	public void put(RankVar var, BigInteger coeff) {
		if (coeff.equals(BigInteger.ZERO)) {
			m_coefficients.remove(var);
		} else {
			m_coefficients.put(var, coeff);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		boolean first = true;
		for (Map.Entry<RankVar, BigInteger> entry : m_coefficients.entrySet()) {
			if (!first) {
				sb.append(entry.getValue().compareTo(BigInteger.ZERO) < 0
						? " - " : " + ");
			} else {
				if (entry.getValue().compareTo(BigInteger.ZERO) < 0) {
					sb.append("-");
				}
			}
			sb.append(entry.getValue().abs());
			sb.append("*");
			sb.append(entry.getKey());
			first = false;
		}
		if (!m_constant.equals(BigInteger.ZERO) || first) {
			if (!first) {
				sb.append(m_constant.compareTo(BigInteger.ZERO) < 0
						? " - " : " + ");
				sb.append(m_constant.abs());
			} else {
				sb.append(m_constant);
			}
		}
		return sb.toString();
	}
	
	private static Term constructSummand(Script script, Term t,
			BigInteger coefficient) {
		if (coefficient.equals(BigInteger.ONE)) {
			return t; 
		} else {
			return script.term("*", script.numeral(coefficient), t);
		}
	}
	
	/**
	 * Return the affine-linear function as a SMTlib term
	 * @param script the current script
	 * @return the generated term
	 * @throws SMTLIBException
	 */
	public Term asTerm(Script script) throws SMTLIBException {
		ArrayList<Term> summands = new ArrayList<Term>();
		for (Map.Entry<RankVar, BigInteger> entry : m_coefficients.entrySet()) {
			summands.add(constructSummand(script,
					entry.getKey().getDefinition(), entry.getValue()));
		}
		summands.add(script.numeral(m_constant));
		return SmtUtils.sum(script, script.sort("Real"),
				summands.toArray(new Term[0]));
	}
	
	/**
	 * Return the affine-linear function as a Boogie AST expression
	 * @param script the current script
	 * @param smt2boogie the variable translation
	 * @return the generated expression
	 */
	public Expression asExpression(Script script, Term2Expression smt2boogie) {
		Term formula = asTerm(script);
		return smt2boogie.translate(formula);
	}
	
	/**
	 * Evaluate this function for a variable assignment
	 * @param assignment the assignment to the variables
	 * @return the value of the function
	 */
	public Rational evaluate(Map<RankVar, Rational> assignment) {
		Rational r = Rational.ZERO;
		for (Map.Entry<RankVar, BigInteger> entry
				: m_coefficients.entrySet()) {
			Rational val = assignment.get(entry.getKey());
			if (val == null) {
				val = Rational.ZERO;
			}
			r.add(val.mul(entry.getValue()));
		}
		r.add(Rational.valueOf(m_constant, BigInteger.ONE));
		return r;
	}
}