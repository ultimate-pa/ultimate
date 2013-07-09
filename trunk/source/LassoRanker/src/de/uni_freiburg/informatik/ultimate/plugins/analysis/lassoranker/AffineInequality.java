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
public class AffineInequality {
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
	private Map<TermVariable, Rational> m_summands;
	
	/**
	 * Affine constant
	 */
	private Rational m_constant;
	
	/**
	 * Construct an empty affine term, i.e. with value 0.
	 */
	public AffineInequality() {
		m_summands = new HashMap<TermVariable, Rational>();
		m_constant = Rational.ZERO;
	}
	
	/**
	 * Construct an affine term from a Term instance.
	 * @throws TermIsNotAffineException if the term was not affine
	 * @param t original term
	 */
	public static AffineInequality fromTerm(Term term, VariableDomain domain)
			throws TermException {
		AffineInequality at;
		if (term instanceof ConstantTerm) {
			at = new AffineInequality();
			at.add(AuxiliaryMethods.convertCT((ConstantTerm) term));
		} else if (term instanceof TermVariable) {
			at = new AffineInequality();
			at.add((TermVariable) term, Rational.ONE);
		} else if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName() == "+") {
				at = fromTerm(appt.getParameters()[0], domain);
				for (int i = 1; i < appt.getParameters().length; ++i)
					at.add(fromTerm(appt.getParameters()[i], domain));
			} else if (appt.getFunction().getName() == "-") {
				if (appt.getFunction().getParameterCount() == 1) {
					// unary minus
					at = fromTerm(appt.getParameters()[0], domain);
					at.mult(Rational.MONE);
				} else { // binary minus (and polyary minus)
					at = fromTerm(appt.getParameters()[0], domain);
					at.mult(Rational.MONE);
					for (int i = 1; i < appt.getParameters().length; ++i)
						at.add(fromTerm(appt.getParameters()[i], domain));
					at.mult(Rational.MONE);
				}
			} else if (appt.getFunction().getName() == "*") {
				at = new AffineInequality();
				at.m_constant = Rational.ONE;
				for (Term u : appt.getParameters()) {
					AffineInequality atu = fromTerm(u, domain);
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
					throw new TermIsNotAffineException("Division is disabled.",
							appt);
				}
				AffineInequality divident = fromTerm(appt.getParameters()[0], domain);
				AffineInequality divisor  = fromTerm(appt.getParameters()[1], domain);
				if (!divisor.isConstant()) {
					throw new TermIsNotAffineException("Non-constant divisor.",
							appt);
				} else if (divisor.m_constant.equals(Rational.ZERO)) {
					throw new TermIsNotAffineException("Division by zero.",
							appt);
				} else {
					at = divident;
					at.mult(divisor.m_constant.inverse());
				}
			} else if (appt.getFunction().getName() == "div") {
				// integer division
				assert(domain == VariableDomain.INTEGERS);
				assert(appt.getParameters().length == 2);
				AffineInequality divident = fromTerm(appt.getParameters()[0], domain);
				AffineInequality divisor  = fromTerm(appt.getParameters()[1], domain);
				
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
					at.mult(divisor.m_constant.inverse());
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
		return m_summands.isEmpty();
	}
	
	/**
	 * @return the constant component
	 */
	public Rational getConstant() {
		return m_constant;
	}
	
	/**
	 * Return a variable's coefficient
	 * @param var a variable
	 * @return zero if the variable does not occur
	 */
	public Rational getCoefficient(TermVariable var) {
		Rational c = m_summands.get(var);
		if (c == null) {
			return Rational.ZERO;
		}
		return c;
	}
	
	/**
	 * @return the collection of variable/coefficient pairs
	 */
	public Map<TermVariable, Rational> getSummands() {
		return m_summands;
	}
	
	/**
	 * @return a collection of all occuring variables
	 */
	public Collection<TermVariable> getVariables() {
		return m_summands.keySet();
	}
	
	/**
	 * Adjoin the summands of another term
	 * @param at another affine term
	 */
	public void add(AffineInequality at) {
		this.add(at.m_constant);
		for (Map.Entry<TermVariable, Rational> entry
				: at.m_summands.entrySet()) {
			this.add(entry.getKey(), entry.getValue());
		}
	}
	
	/**
	 * Add another summand to the affine term
	 * @param var a variable
	 * @param r coefficient
	 */
	public void add(TermVariable var, Rational r) {
		if (m_summands.containsKey(var)) {
			Rational c = m_summands.get(var).add(r);
			m_summands.put(var, c);
			if (c.equals(Rational.ZERO)) {
				m_summands.remove(var);
			}
		} else {
			m_summands.put(var, r);
		}
	}
	
	/**
	 * Add a constant to the affine term
	 * @param r a constant
	 */
	public void add(Rational r) {
		m_constant = m_constant.add(r);
	}
	
	/**
	 * Multiply with a constant
	 * @param r factor
	 */
	public void mult(Rational r) {
		m_constant = m_constant.mul(r);
		if (r.equals(Rational.ZERO)) {
			m_summands.clear();
		} else {
			for (Map.Entry<TermVariable, Rational> entry
					: m_summands.entrySet()) {
				m_summands.put(entry.getKey(), entry.getValue().mul(r));
			}
		}
	}
	
	@Override
	public String toString() {
		String result = "";
		for (Map.Entry<TermVariable, Rational> entry : m_summands.entrySet()) {
			result += entry.getValue().isNegative() ? " - " : " + ";
			result += entry.getValue().abs() + "*" + entry.getKey();
		}
		if (!m_constant.equals(Rational.ZERO) || result.isEmpty()) {
			if (m_constant.isNegative() || !result.isEmpty()) {
				result += m_constant.isNegative() ? " - " : " + ";
			}
			result += m_constant.abs();
		}
		if (result.charAt(0) == ' ') {
			result = result.substring(1); // Drop first space
		}
		
		return result;
	}
}
