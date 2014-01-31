package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.io.Serializable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.model.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie.Smt2Boogie;

/**
 * This represents a linear supporting invariant of the form
 * Σ c_i x_i + c >= 0.
 * 
 * @author Jan Leike
 */
public class SupportingInvariant implements Serializable {
	
	private static final long serialVersionUID = -8409937196513651751L;
	
	Map<BoogieVar, BigInteger> m_coefficients;
	BigInteger m_constant;
	
	public SupportingInvariant() {
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
	
	/**
	 * Check if this supporting invariant is the trivial invariant "true".
	 */
	public boolean isTrivial() {
		return m_constant.compareTo(BigInteger.ZERO) >= 0
				&& m_coefficients.isEmpty();
	}
	
	/**
	 * Check whether this supporting invariant is equivalent to "false".
	 */
	public boolean isFalse() {
		return m_constant.compareTo(BigInteger.ZERO) < 0
				&& m_coefficients.isEmpty();
	}
	
	/**
	 * Return a string representation of the supporting invariant. 
	 */
	@Override
	public String toString() {
		if (m_coefficients.isEmpty()) {
			return m_constant + " >= 0";
		}
		String res = "";
		boolean first = true;
		for (Map.Entry<BoogieVar, BigInteger> entry
				: m_coefficients.entrySet()) {
			if (!first) {
				res += entry.getValue().compareTo(BigInteger.ZERO) < 0
						? " - " : " + ";
			} else {
				if (entry.getValue().compareTo(BigInteger.ZERO) < 0) {
					res += "-";
				}
			}
			res += entry.getValue().abs() + "*" + entry.getKey();
			first = false;
		}
		res += " + " + m_constant;
		return res + " >= 0";
	}
	
	/**
	 * Return the supporting invariant in form of a SMTLib term.
	 * @param script the current script
	 * @return the supporting invariant
	 */
	public Term asTerm(Script script, Smt2Boogie smt2boogie)
			throws SMTLIBException {
		ArrayList<Term> summands = new ArrayList<Term>();
		ArrayList<Term> lhs = new ArrayList<Term>();
		ArrayList<Term> rhs = new ArrayList<Term>();
		for (Map.Entry<BoogieVar, BigInteger> entry	: m_coefficients.entrySet()) {
			if (entry.getValue().compareTo(BigInteger.ZERO) >= 0) {
				Term summand = constructSummand(script, entry.getKey().getTermVariable(), entry.getValue());
				lhs.add(summand);
			} else {
				BigInteger coefficient = entry.getValue().abs();
				Term summand = constructSummand(script, entry.getKey().getTermVariable(), coefficient);
				rhs.add(summand);
			}
		}
		if (m_constant.compareTo(BigInteger.ZERO) >= 0) {
			lhs.add(script.numeral(m_constant));
		} else {
			rhs.add(script.numeral(m_constant.abs()));
		}
		summands.add(script.numeral(m_constant));
		Term lhsTerm = UtilExperimental.sum(script, lhs.toArray(new Term[0]));
		Term rhsTerm = UtilExperimental.sum(script, rhs.toArray(new Term[0]));
		return script.term(">=", lhsTerm, rhsTerm);
	}
	
	private static Term constructSummand(Script script, TermVariable tv, BigInteger coefficient ) {
		if (coefficient.equals(BigInteger.ONE)) {
			return tv; 
		} else {
			return script.term("*", script.numeral(coefficient), tv);
		}
	}
	
	public Expression asExpression(Script script, Smt2Boogie smt2boogie) {
		Term formula = asTerm(script, smt2boogie);
		return smt2boogie.translate(formula);
	}
}