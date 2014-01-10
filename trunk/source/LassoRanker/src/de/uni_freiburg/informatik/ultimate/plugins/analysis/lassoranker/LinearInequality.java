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
 * where c_i, c are affine terms possibly containing other variables,
 * x_i are variables and ⊳ is > or ≥.
 * 
 * The variables x_i used here are program variables, while the variables
 * contained in the affine terms c_i, c are parameters from the ranking
 * function / supporting invariant templates. After the Motzkin transformation,
 * the program variables x_i will be eliminated while the parameters in c_i, c
 * persist. This is why they are separated in this data structure.
 * 
 * @author Jan Leike
 */
public class LinearInequality {
	
	/**
	 * Whether the inequality is strict (">") versus non-strict ("≥")
	 */
	private boolean m_strict = false;
	
	/**
	 * Whether this inequality needs its own Motzkin coefficient
	 */
	public boolean needs_motzkin_coefficient = true;
	
	/**
	 * List of variables including rational coefficients
	 */
	private Map<TermVariable, AffineTerm> m_coefficients;
	
	/**
	 * Affine constant
	 */
	private AffineTerm m_constant;
	
	/**
	 * Construct an empty linear inequality, i.e. 0 ≥ 0.
	 */
	public LinearInequality() {
		m_coefficients = new HashMap<TermVariable, AffineTerm>();
		m_constant = new AffineTerm();
	}
	
	/**
	 * Construct an linear inequality from a Term instance.
	 * @param term an affine-linear sum of values with termvariables
	 * @throws TermIsNotAffineException if the term was not an affine-linear sum 
	 */
	public static LinearInequality fromTerm(Term term)
			throws TermException {
		LinearInequality li;
		if (term instanceof ConstantTerm) {
			li = new LinearInequality();
			li.add(new AffineTerm(AuxiliaryMethods.convertCT((ConstantTerm)
					term)));
		} else if (term instanceof TermVariable) {
			li = new LinearInequality();
			li.add((TermVariable) term, Rational.ONE);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName() == "+") {
				li = fromTerm(appt.getParameters()[0]);
				for (int i = 1; i < appt.getParameters().length; ++i)
					li.add(fromTerm(appt.getParameters()[i]));
			} else if (appt.getFunction().getName() == "-") {
				if (appt.getFunction().getParameterSorts().length == 1) {
					// unary minus
					li = fromTerm(appt.getParameters()[0]);
					li.mult(Rational.MONE);
				} else { // binary minus (and polyary minus)
					li = fromTerm(appt.getParameters()[0]);
					li.mult(Rational.MONE);
					for (int i = 1; i < appt.getParameters().length; ++i)
						li.add(fromTerm(appt.getParameters()[i]));
					li.mult(Rational.MONE);
				}
			} else if (appt.getFunction().getName() == "*") {
				li = new LinearInequality();
				li.m_constant = new AffineTerm(Rational.ONE);
				for (Term u : appt.getParameters()) {
					LinearInequality liu = fromTerm(u);
					if (li.isConstant() && li.m_constant.isConstant()) {
						liu.mult(li.m_constant.getConstant());
						li = liu;
					} else if (liu.isConstant() && liu.m_constant.isConstant()) {
						li.mult(liu.m_constant.getConstant());
					} else {
						throw new TermIsNotAffineException(
								"Product with more than one non-constant " +
								"factors found.", appt);
					}
				}
			} else if (appt.getFunction().getName() == "/") {
				assert(appt.getParameters().length == 2);
				LinearInequality divident = fromTerm(appt.getParameters()[0]);
				LinearInequality divisor  = fromTerm(appt.getParameters()[1]);
				if (!divisor.isConstant() || !divisor.m_constant.isConstant()) {
					throw new TermIsNotAffineException("Non-constant divisor.",
							appt);
				} else if (divisor.m_constant.equals(Rational.ZERO)) {
					throw new TermIsNotAffineException("Division by zero.",
							appt);
				} else {
					li = divident;
					li.mult(divisor.m_constant.getConstant().inverse());
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
	public AffineTerm getConstant() {
		return m_constant;
	}
	
	/**
	 * Is this a strict inequality?
	 */
	public boolean isStrict() {
		return m_strict;
	}
	
	/**
	 * Set whether this is a strict inequality
	 */
	public void setStrict(boolean strict) {
		m_strict = strict;
	}
	
	/**
	 * Returns '>' if this is a strict inequality and '>=' otherwise
	 */
	public String getInequalitySymbol() {
		return m_strict ? ">" : ">=";
	}
	
	/**
	 * Returns '<' if this is a strict inequality and '<=' otherwise
	 */
	public String getInequalitySymbolReverse() {
		return m_strict ? "<" : "<=";
	}
	
	/**
	 * Return a variable's coefficient
	 * @param var a variable
	 * @return zero if the variable does not occur
	 */
	public AffineTerm getCoefficient(TermVariable var) {
		AffineTerm p = m_coefficients.get(var);
		if (p == null) {
			return new AffineTerm();
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
		for (Map.Entry<TermVariable, AffineTerm> entry
				: li.m_coefficients.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * Add another coefficients to the linear inequality
	 * @param var variable
	 * @param t   the variable's coefficient to be added
	 */
	public void add(TermVariable var, AffineTerm a) {
		AffineTerm a2 = m_coefficients.get(var);
		if (a2 != null) {
			a2.add(a);
			if (!a2.isZero()) {
				m_coefficients.put(var, a2);
			} else {
				m_coefficients.remove(var);
			}
		} else {
			if (!a.isZero()) {
				m_coefficients.put(var, a);
			}
		}
	}
	
	/**
	 * Add another coefficients to the linear inequality
	 * @param var variable
	 * @param t   the variable's coefficient to be added
	 */
	public void add(TermVariable var, Rational r) {
		this.add(var, new AffineTerm(r));
	}
	
	/**
	 * Add a constant to the linear inequality
	 * @param t a constant
	 */
	public void add(AffineTerm p) {
		m_constant.add(p);
	}
	
	/**
	 * Multiply with a constant
	 * @param t factor
	 */
	public void mult(Rational r) {
		m_constant.mult(r);
		for (Map.Entry<TermVariable, AffineTerm> entry
				: m_coefficients.entrySet()) {
			entry.getValue().mult(r);
		}
	}
	
	/**
	 * Negate the linear inequality
	 * <pre>
	 * a ≥ b --> b > a
	 * a > b --> b ≥ a
	 * </pre>
	 */
	public void negate() {
		mult(Rational.MONE);
		m_strict = !m_strict;
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("0 ");
		sb.append(getInequalitySymbolReverse());
		sb.append(" ");
		boolean first = true;
		for (Map.Entry<TermVariable, AffineTerm> entry
				: m_coefficients.entrySet()) {
			if (entry.getValue().isZero()) {
				continue;
			}
			String param = entry.getValue().toString();
			if (param.startsWith("-")) {
				if (!first) {
					sb.append(" - ");
					sb.append(param.substring(1));
				} else {
					sb.append(param);
				}
			} else {
				if (!first) {
					sb.append(" + ");
				}
				sb.append(param);
			}
			sb.append("*");
			sb.append(entry.getKey());
			first = false;
		}
		if (!m_constant.isZero() || first) {
			String s = m_constant.toString();
			if (s.startsWith("-")) {
				if (!first) {
					sb.append(" - ");
					sb.append(s.substring(1));
				} else {
					sb.append(s);
				}
			} else {
				if (!first) {
					sb.append(" + ");
				}
				sb.append(s);
			}
		}
		return sb.toString();
	}
}