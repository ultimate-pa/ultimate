package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.*;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences.UseDivision;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences.VariableDomain;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermIsNotAffineException;


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
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	/**
	 * Whether the inequality is strict ("<" versus "≤")
	 */
	public enum Inequality {
		LESS_THAN,         // "<"
		LESS_THAN_OR_EQUAL // "≤"
	}
	
	/**
	 * Whether the inequality is strict ("<" versus "<=")
	 */
	public Inequality ieqsymb = Inequality.LESS_THAN_OR_EQUAL;
	
	/**
	 * List of variables including rational coefficients
	 */
	private Map<TermVariable, Term> m_coefficients;
	
	/**
	 * Affine constant
	 */
	private Term m_constant;
	
	/**
	 * SMT script
	 */
	private Script m_script;
	
	/**
	 * Construct an empty linear inequality, i.e. 0 ≤ 0.
	 */
	public LinearInequality(Script script) {
		m_script = script;
		m_coefficients = new HashMap<TermVariable, Term>();
		m_constant = m_script.decimal("0");
	}
	
	/**
	 * Construct an linear inequality from a Term instance.
	 * @throws TermIsNotAffineException if the term was not an affine-linear sum
	 * @param term an affine-linear sum of values with termvariables
	 * @param domain variable domain to be used during construction 
	 */
	public static LinearInequality fromTerm(Script script, Term term, VariableDomain domain)
			throws TermException {
		LinearInequality at;
		if (term instanceof ConstantTerm) {
			at = new LinearInequality(script);
			at.add(term);
		} else if (term instanceof TermVariable) {
			at = new LinearInequality(script);
			at.add((TermVariable) term, script.decimal("1"));
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName() == "+") {
				at = fromTerm(script, appt.getParameters()[0], domain);
				for (int i = 1; i < appt.getParameters().length; ++i)
					at.add(fromTerm(script, appt.getParameters()[i], domain));
			} else if (appt.getFunction().getName() == "-") {
				if (appt.getFunction().getParameterCount() == 1) {
					// unary minus
					at = fromTerm(script, appt.getParameters()[0], domain);
					at.mult(script.decimal("-1"));
				} else { // binary minus (and polyary minus)
					at = fromTerm(script, appt.getParameters()[0], domain);
					at.mult(script.decimal("-1"));
					for (int i = 1; i < appt.getParameters().length; ++i)
						at.add(fromTerm(script, appt.getParameters()[i],
								domain));
					at.mult(script.decimal("-1"));
				}
			} else if (appt.getFunction().getName() == "*") {
				at = new LinearInequality(script);
				at.m_constant = script.decimal("1");
				for (Term u : appt.getParameters()) {
					LinearInequality atu = fromTerm(script, u, domain);
					if (at.isConstant()) {
						atu.mult(at.m_constant);
						at = atu;
					} else if (atu.isConstant()) {
						at.mult(atu.m_constant);
					} else {
						throw new TermIsNotAffineException(
								"Product with more than one non-constant " +
								"factors found.", appt);
					}
				}
			} else if (appt.getFunction().getName() == "/") {
				// real division
				assert(domain == VariableDomain.REALS);
				assert(appt.getParameters().length == 2);
				if (Preferences.use_division == UseDivision.DISABLED) {
					throw new TermException("Division is disabled.",
							appt);
				}
				LinearInequality divident = fromTerm(script,
						appt.getParameters()[0], domain);
				LinearInequality divisor  = fromTerm(script,
						appt.getParameters()[1], domain);
				if (!divisor.isConstant()) {
					throw new TermIsNotAffineException("Non-constant divisor.",
							appt);
				} else if (divisor.m_constant.equals(Rational.ZERO)) {
					throw new TermIsNotAffineException("Division by zero.",
							appt);
				} else {
					at = divident;
					at.mult(script.term("/", script.decimal("1"),
							divisor.m_constant));
				}
			} else if (appt.getFunction().getName() == "div") {
				// integer division
				assert(domain == VariableDomain.INTEGERS);
				assert(appt.getParameters().length == 2);
				LinearInequality divident = fromTerm(script,
						appt.getParameters()[0], domain);
				LinearInequality divisor  = fromTerm(script,
						appt.getParameters()[1], domain);
				
				if (Preferences.use_division == UseDivision.SAFE) {
					s_Logger.warn("The currently configured semantics of " +
							"integer division follows slightly unsual " +
							"rules: the program may only proceed if the " +
							"division has no remainder.");
				} else if (Preferences.use_division == UseDivision.C_STYLE) {
					throw new UnsupportedOperationException(
							"C-style division is not implemented yet.");
					// TODO: this requires more work; divisions must be
					// removed and applied to tmp vars in a separate step.
				} else {
					throw new TermIsNotAffineException(
							"Division is disabled for Integers.", appt);
				}
				
				if (!divisor.isConstant()) {
					throw new TermIsNotAffineException("Non-constant divisor.",
							appt);
				} else if (divisor.m_constant.equals(Rational.ZERO)) {
					throw new TermIsNotAffineException("Division by zero.",
							appt);
				} else {
					at = divident;
					at.mult(script.term("/", script.decimal("1"),
							divisor.m_constant));
				}
			} else {
				throw new TermIsNotAffineException(
						"Stumbled upon an unknown function symbol.", appt);
			}
		} else {
			throw new TermIsNotAffineException(
						"Stumbled upon a Term of unknown subclass.", term);
		}
		return at;
	}
	
	/**
	 * @return true iff the affine term is just a constant
	 */
	public boolean isConstant() {
		return m_coefficients.isEmpty();
	}
	
	/**
	 * @return the constant component
	 */
	public Term getConstant() {
		return m_constant;
	}
	
	/**
	 * Return a variable's coefficient
	 * @param var a variable
	 * @return zero if the variable does not occur
	 */
	public Term getCoefficient(TermVariable var) {
		Term t = m_coefficients.get(var);
		if (t == null) {
			return m_script.decimal("0");
		}
		return t;
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
		for (Map.Entry<TermVariable, Term> entry
				: li.m_coefficients.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * Add another coefficients to the linear inequality
	 * @param var variable
	 * @param t   the variable's coefficient to be added
	 */
	public void add(TermVariable var, Term t) {
		if (m_coefficients.containsKey(var)) {
			Term t2 = Util.sum(m_script, m_coefficients.get(var), t);
			m_coefficients.put(var, t2);
		} else {
			m_coefficients.put(var, t);
		}
	}
	
	/**
	 * Add a constant to the linear inquality
	 * @param t a constant
	 */
	public void add(Term t) {
		m_constant = Util.sum(m_script, m_constant, t);
	}
	
	/**
	 * Multiply with a constant
	 * @param t factor
	 */
	public void mult(Term t) {
		m_constant = m_script.term("*", m_constant, t);
		for (Map.Entry<TermVariable, Term> entry
				: m_coefficients.entrySet()) {
			Term t2 = m_script.term("*", entry.getValue(), t);
			m_coefficients.put(entry.getKey(), t2);
		}
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		for (Map.Entry<TermVariable, Term> entry : m_coefficients.entrySet()) {
			sb.append(entry.getValue());
			sb.append("*");
			sb.append(entry.getKey());
			sb.append(" + ");
		}
		sb.append(m_constant);
		if (ieqsymb == Inequality.LESS_THAN) {
			sb.append(" < 0");
		} else if (ieqsymb == Inequality.LESS_THAN_OR_EQUAL) {
			sb.append(" <= 0");
		} else {
			assert(false);
		}
		return sb.toString();
	}
}
