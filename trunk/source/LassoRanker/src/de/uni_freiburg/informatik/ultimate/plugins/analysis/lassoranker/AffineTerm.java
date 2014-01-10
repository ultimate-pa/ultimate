package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;


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
public class AffineTerm {
	private Rational m_Constant;
	private Map<Term, Rational> m_Coefficients;
	
	/**
	 * Construct the affine term 0
	 */
	public AffineTerm() {
		m_Coefficients = new HashMap<Term, Rational>();
		m_Constant = Rational.ZERO;
	}
	
	/**
	 * Construct an affine term from a constant
	 */
	public AffineTerm(Rational r) {
		m_Coefficients = new HashMap<Term, Rational>();
		m_Constant = r;
	}
	
	/**
	 * Construct an affine term from a variable with coefficient
	 */
	public AffineTerm(Term var, Rational r) {
		m_Coefficients = new HashMap<Term, Rational>();
		m_Constant = Rational.ZERO;
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
	 * @return the affine term as a term of sort "Real"
	 */
	public Term asRealTerm(Script script) {
		Term[] summands = new Term[m_Coefficients.size() + 1];
		int i = 0;
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			Term coeff = AuxiliaryMethods.rationalToDecimal(script,
					entry.getValue());
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		summands[i] = AuxiliaryMethods.rationalToDecimal(script, m_Constant);
		return UtilExperimental.sum(script, script.sort("Real"), summands);
	}
	
	/**
	 * @param script current SMT script
	 * @return the affine term as a term of sort "Int"
	 */
	public Term asIntTerm(Script script) {
		Term[] summands = new Term[m_Coefficients.size() + 1];
		int i = 0;
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			Term coeff = AuxiliaryMethods.rationalToNumeral(script,
					entry.getValue());
			summands[i] = script.term("*", coeff, entry.getKey());
			++i;
		}
		summands[i] = AuxiliaryMethods.rationalToNumeral(script, m_Constant);
		return UtilExperimental.sum(script, script.sort("Int"), summands);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Map.Entry<Term, Rational> entry : m_Coefficients.entrySet()) {
			sb.append(entry.getValue().isNegative() ? " - " : " + ");
			sb.append(entry.getValue().abs() + "*" + entry.getKey());
		}
		if (!m_Constant.equals(Rational.ZERO) || sb.length() == 0) {
			if (m_Constant.isNegative() || sb.length() > 0) {
				sb.append(m_Constant.isNegative() ? " - " : " + ");
			}
			sb.append(m_Constant.abs());
		}
		String result = sb.toString();
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}
		
		return result;
	}
}