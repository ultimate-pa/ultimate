package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;


/**
 * A parameter in the linear inequality consists of a rational coefficient
 * and possibly a free variable
 * 
 * @author Jan Leike
 */
public class ParameterizedRational {
	public Rational coefficient;
	public Term variable;
	
	/**
	 * Construct the parameter 0
	 */
	public ParameterizedRational() {
		variable = null;
		coefficient = Rational.ZERO;
	}
	
	/**
	 * Construct a parameter from a constant
	 */
	public ParameterizedRational(Rational r) {
		variable = null;
		coefficient = r;
	}
	
	/**
	 * Construct a parameter from a variable
	 */
	public ParameterizedRational(Term var) {
		assert(var instanceof ApplicationTerm);
		assert(((ApplicationTerm) var).getParameters().length == 0);
		variable = var;
		coefficient = Rational.ONE;
	}
	
	/**
	 * @return whether this is just a rational constant
	 */
	public boolean isConstant() {
		return variable == null;
	}
	
	/**
	 * @return whether this is zero
	 */
	public boolean isZero() {
		return variable == null && coefficient.equals(Rational.ZERO);
	}
	
	/**
	 * Add another parameter to this.
	 * Note: the variables have to be the same!
	 */
	public void add(ParameterizedRational p) {
		if (coefficient.equals(Rational.ZERO)) {
			variable = p.variable;
		}
		assert(p.coefficient.equals(Rational.ZERO) || p.variable == variable);
		coefficient = coefficient.add(p.coefficient);
		if (coefficient.equals(Rational.ZERO)) {
			variable = null;
		}
	}
	
	/**
	 * @param script current SMT script
	 * @return the parameter as a term of sort "Real"
	 */
	public Term asRealTerm(Script script) {
		Term c = AuxiliaryMethods.rationalToDecimal(script, coefficient);
		if (variable == null) {
			return c;
		}
		return script.term("*", c, variable);
	}
	
	/**
	 * @param script current SMT script
	 * @return the parameter as a term of sort "Int"
	 */
	public Term asIntTerm(Script script) {
		Term c = AuxiliaryMethods.rationalToNumeral(script, coefficient);
		if (variable == null) {
			return c;
		}
		return script.term("*", c, variable);
	}
	
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append(coefficient);
		if (variable != null) {
			sb.append("*");
			sb.append(variable);
		}
		return sb.toString();
	}
}