package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions;

import java.math.BigInteger;
import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;


/**
 * A simple linear ranking function.
 * 
 * @author Jan Leike
 */
public class LinearRankingFunction implements RankingFunction {
	
	private static final long serialVersionUID = 5376322220596462295L;
	
	private Map<BoogieVar, BigInteger> m_coefficients;
	private BigInteger m_constant;
	
	public LinearRankingFunction() {
		m_coefficients = new HashMap<BoogieVar, BigInteger>();
		m_constant = BigInteger.ZERO;
	}
	
	/**
	 * Set a coefficient for a variable.
	 */
	public void put(BoogieVar var, BigInteger coeff) {
		if (coeff.equals(BigInteger.ZERO)) {
			m_coefficients.remove(var);
		} else {
			m_coefficients.put(var, coeff);
		}
	}
	
	/**
	 * Set the constant.
	 */
	public void setConstant(BigInteger c) {
		m_constant = c;
	}
	
	/**
	 * Return the coefficients corresponding to this variable
	 */
	public BigInteger get(BoogieVar var) {
		return m_coefficients.get(var);
	}
	
	/**
	 * Return the linear coefficients.
	 */
	public Map<BoogieVar, BigInteger> getCoefficients() {
		return m_coefficients;
	}
	
	/**
	 * Return the constant
	 */
	public BigInteger getConstant() {
		return m_constant;
	}
	
	@Override
	public String toString() {
		if (m_coefficients.isEmpty()) {
			return "f = 0";
		}
		String s = "f(";
		boolean first = true;
		for (BoogieVar var : m_coefficients.keySet()) {
			if (!first) {
				s += ", ";
			}
			s += var.getIdentifier();
			first = false;
		}
		s += ") = ";
		first = true;
		for (Map.Entry<BoogieVar, BigInteger> entry
				: m_coefficients.entrySet()) {
			if (!first) {
				s += entry.getValue().compareTo(BigInteger.ZERO) < 0
						? " - " : " + ";
			} else {
				if (entry.getValue().compareTo(BigInteger.ZERO) < 0) {
					s += "-";
				}
			}
			s += entry.getValue().abs() + "*" + entry.getKey();
			first = false;
		}
		if (m_constant != BigInteger.ZERO) {
			s += m_constant.compareTo(BigInteger.ZERO) < 0 ? " - " : " + ";
			s += m_constant.abs();
		}
		return s;
	}
	
	@Override
	public Term asFormula(Script script, Smt2Boogie smt2boogie)
			throws SMTLIBException {
		ArrayList<Term> summands = new ArrayList<Term>(m_coefficients.size()+1);
		for (Map.Entry<BoogieVar, BigInteger> entry
				: m_coefficients.entrySet()) {
			Term summand;
			if (entry.getValue().equals(BigInteger.ONE)) {
				summand = entry.getKey().getTermVariable();
			} else if (entry.getValue().equals(BigInteger.valueOf(-1))) {
				summand = script.term("-", entry.getKey().getTermVariable());
			} else {
				summand = script.term("*",
						script.numeral(entry.getValue()),
						entry.getKey().getTermVariable());
			}
			summands.add(summand);
		}
		if (!m_constant.equals(BigInteger.ZERO) || summands.size() == 0) {
			summands.add(script.numeral(m_constant));
		}
		if (summands.size() == 1) {
			return summands.get(0);
		} else {
			return script.term("+", summands.toArray(new Term[0]));
		}
	}
	
	public Expression asExpression(Script script, Smt2Boogie smt2boogie) {
		Term formula = asFormula(script, smt2boogie);
		return smt2boogie.translate(formula);
	}
	
	@Override
	public Rational evaluate(Map<BoogieVar, Rational> assignment) {
		Rational r = Rational.ZERO;
		for (Map.Entry<BoogieVar, BigInteger> entry
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
