package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermIsNotAffineException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.UnknownFunctionException;


/**
 * This represents an affine-linear inequality of the form
 * 
 * <pre>Σ c_i * x_i + c ⊳ 0</pre>
 * 
 * where c_i, c are rational constants,
 * x_i are variables and ⊳ is > or ≥.
 * 
 * Note that there is a class
 * de.uni_freiburg.informatik.ultimate.smtinterpol.convert.AffineTerm
 * which is similar but unusable in this case because it is closely
 * interwoven with the SMTLIB interiors.
 * 
 * @author Jan Leike
 */
public class LinearInequality {
	
	/**
	 * Whether the inequality is strict ("<") versus non-strict ("<=")
	 */
	public boolean strict = false;
	
	/**
	 * Whether this inequality needs its own Motzkin coefficient
	 */
	public boolean m_needs_motzkin_coefficient = true;
	
	/**
	 * List of variables including rational coefficients
	 */
	private Map<TermVariable, ParameterizedRational> m_coefficients;
	
	/**
	 * Affine constant
	 */
	private ParameterizedRational m_constant;
	
	/**
	 * Construct an empty linear inequality, i.e. 0 ≤ 0.
	 */
	public LinearInequality() {
		m_coefficients = new HashMap<TermVariable, ParameterizedRational>();
		m_constant = new ParameterizedRational();
	}
	
	/**
	 * Construct an linear inequality from a Term instance.
	 * @throws TermIsNotAffineException if the term was not an affine-linear sum
	 * @param term an affine-linear sum of values with termvariables
	 * @param domain variable domain to be used during construction 
	 */
	public static LinearInequality fromTerm(Script script, Term term)
			throws TermException {
		LinearInequality li;
		if (term instanceof ConstantTerm) {
			li = new LinearInequality();
			li.add(new ParameterizedRational(AuxiliaryMethods.convertCT((ConstantTerm)
					term)));
		} else if (term instanceof TermVariable) {
			li = new LinearInequality();
			li.add((TermVariable) term, Rational.ONE);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName() == "+") {
				li = fromTerm(script, appt.getParameters()[0]);
				for (int i = 1; i < appt.getParameters().length; ++i)
					li.add(fromTerm(script, appt.getParameters()[i]));
			} else if (appt.getFunction().getName() == "-") {
				if (appt.getFunction().getParameterCount() == 1) {
					// unary minus
					li = fromTerm(script, appt.getParameters()[0]);
					li.mult(Rational.MONE);
				} else { // binary minus (and polyary minus)
					li = fromTerm(script, appt.getParameters()[0]);
					li.mult(Rational.MONE);
					for (int i = 1; i < appt.getParameters().length; ++i)
						li.add(fromTerm(script, appt.getParameters()[i]));
					li.mult(Rational.MONE);
				}
			} else if (appt.getFunction().getName() == "*") {
				li = new LinearInequality();
				li.m_constant = new ParameterizedRational(Rational.ONE);
				for (Term u : appt.getParameters()) {
					LinearInequality liu = fromTerm(script, u);
					if (li.isConstant()) {
						liu.mult(li.m_constant.coefficient);
						li = liu;
					} else if (liu.isConstant()) {
						li.mult(liu.m_constant.coefficient);
					} else {
						throw new TermIsNotAffineException(
								"Product with more than one non-constant " +
								"factors found.", appt);
					}
				}
			} else if (appt.getFunction().getName() == "/") {
				assert(appt.getParameters().length == 2);
				LinearInequality divident = fromTerm(script,
						appt.getParameters()[0]);
				LinearInequality divisor  = fromTerm(script,
						appt.getParameters()[1]);
				if (!divisor.isConstant()) {
					throw new TermIsNotAffineException("Non-constant divisor.",
							appt);
				} else if (divisor.m_constant.equals(Rational.ZERO)) {
					throw new TermIsNotAffineException("Division by zero.",
							appt);
				} else {
					li = divident;
					li.mult(divisor.m_constant.coefficient.inverse());
				}
			} else {
				throw new UnknownFunctionException(appt);
			}
		} else {
			throw new TermException("Stumbled upon a Term of unknown subclass.",
					term);
		}
		return li;
	}
	
	/**
	 * @return true iff the affine term is just a constant
	 */
	public boolean isConstant() {
		return m_coefficients.isEmpty() && m_constant.isConstant();
	}
	
	/**
	 * @return the constant component
	 */
	public ParameterizedRational getConstant() {
		return m_constant;
	}
	
	/**
	 * Return a variable's coefficient
	 * @param var a variable
	 * @return zero if the variable does not occur
	 */
	public ParameterizedRational getCoefficient(TermVariable var) {
		ParameterizedRational p = m_coefficients.get(var);
		if (p == null) {
			return new ParameterizedRational(Rational.ZERO);
		}
		return p;
	}
	
	/**
	 * @return a collection of all occuring variables
	 */
	public Collection<TermVariable> getVariables() {
		return m_coefficients.keySet();
	}
	
	/**
	 * Add another linear inequality
	 * @param li other linear inequality
	 */
	public void add(LinearInequality li) {
		this.add(li.m_constant);
		for (Map.Entry<TermVariable, ParameterizedRational> entry
				: li.m_coefficients.entrySet()) {
			add(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * Add another coefficients to the linear inequality
	 * @param var variable
	 * @param t   the variable's coefficient to be added
	 */
	public void add(TermVariable var, Rational r) {
		if (m_coefficients.containsKey(var)) {
			m_coefficients.get(var).add(new ParameterizedRational(r));
		} else {
			m_coefficients.put(var, new ParameterizedRational(r));
		}
	}
	
	/**
	 * Add another coefficients to the linear inequality
	 * @param var variable
	 * @param t   the variable's coefficient to be added
	 */
	public void add(TermVariable var, ParameterizedRational p) {
		if (m_coefficients.containsKey(var)) {
			m_coefficients.get(var).add(p);
		} else {
			m_coefficients.put(var, p);
		}
	}
	
	/**
	 * Add a constant to the linear inquality
	 * @param t a constant
	 */
	public void add(ParameterizedRational p) {
		m_constant.add(p);
	}
	
	/**
	 * Multiply with a constant
	 * @param t factor
	 */
	public void mult(Rational r) {
		m_constant.coefficient = m_constant.coefficient.mul(r);
		for (Map.Entry<TermVariable, ParameterizedRational> entry
				: m_coefficients.entrySet()) {
			entry.getValue().coefficient = entry.getValue().coefficient.mul(r);
		}
	}
	
	/**
	 * Negate the linear inequality
	 * <pre>
	 * a ≤ b --> b < a
	 * a < b --> b ≤ a
	 * </pre>
	 */
	public void negate() {
		mult(Rational.MONE);
		strict = !strict;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Map.Entry<TermVariable, ParameterizedRational> entry
				: m_coefficients.entrySet()) {
			sb.append(entry.getValue());
			sb.append("*");
			sb.append(entry.getKey());
			sb.append(" + ");
		}
		sb.append(m_constant);
		sb.append(strict ? " < 0" : " <= 0");
		return sb.toString();
	}
}