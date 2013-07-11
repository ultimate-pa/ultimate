package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


/**
 * Creates and extracts supporting invariants.
 * This class is the counterpart of the RankingFunctionTemplate classes for
 * supporting invariants.
 * 
 * @author Jan Leike
 */
public class SupportingInvariantGenerator extends InstanceCounting {
	
	private static final String s_prefix = "si_";
	private static final String s_const  = "si0_";
	
	private Script m_script;
	
	private Term m_constant;
	private Map<BoogieVar, Term> m_coefficients;
	
	public boolean strict;
	
	/**
	 * @param script The SMTLib script
	 * @param variables A collection of all variables that are relevant for
	 *                   the supporting invariant
	 * @param notNonDecreasing Whether the supporting invariant has to be
	 *                         non-decreasing. (Enabling this requires a
	 *                         non-linear solver!)
	 */
	SupportingInvariantGenerator(Script script,
			Collection<BoogieVar> variables, boolean strict) {
		m_script = script;
		
		// Create variables
		m_constant = AuxiliaryMethods.newRealConstant(m_script,
				s_const + m_instance);
		m_coefficients = new HashMap<BoogieVar, Term>();
		for (BoogieVar var : variables) {
			m_coefficients.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix + m_instance + "_" + var.getGloballyUniqueId()));
		}
		this.strict = strict;
	}
	
	/**
	 * Generate the linear inequality
	 * @param vars a mapping from Boogie variables to TermVariables to be used
	 * @return Linear inequality corresponding to si(x)
	 */
	public LinearInequality generate(Map<BoogieVar, TermVariable> vars) {
		LinearInequality li = new LinearInequality();
		for (Entry<BoogieVar, TermVariable> entry : vars.entrySet()) {
			li.add(entry.getValue(), new LinearInequality.Parameter(m_coefficients.get(entry.getKey())));
		}
		li.m_needs_motzkin_coefficient = false;
		li.strict = this.strict;
		return li;
	}
	
	/**
	 * Return all SMT variables used by this template
	 */
	public Collection<Term> getVariables() {
		Collection<Term> vars = new ArrayList<Term>();
		vars.addAll(m_coefficients.values());
		vars.add(m_constant);
		return vars;
	}
	
	/**
	 * Extract the supporting invariant from a model
	 * @return supporting invariant
	 * @throws SMTLIBException
	 */
	public SupportingInvariant extractSupportingInvariant(Map<Term, Rational> val)
			throws SMTLIBException {
		// Extract coefficients from the model and convert them to Rational
		Rational coeff0 = val.get(m_constant);
		Rational gcd = Rational.ONE.gcd(coeff0);
		Map<BoogieVar, Rational> coeff_val = new HashMap<BoogieVar, Rational>();
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			Rational coeff = val.get(entry.getValue());
			coeff_val.put(entry.getKey(), coeff);
			gcd = coeff.gcd(gcd);
		}
		
		// Multiply all coefficients with the greatest common denominator
		// Note: Because the supporting invariant is an affine term, multiplying
		//       it with a rational is an equivalence transformation.
		coeff0 = coeff0.div(gcd);
		for (Map.Entry<BoogieVar, Rational> entry : coeff_val.entrySet()) {
			assert(entry.getValue().div(gcd).denominator().equals(
					BigInteger.ONE));
			coeff_val.put(entry.getKey(), entry.getValue().div(gcd));
		}
		
		// Construct the supporting invariant object
		SupportingInvariant si = new SupportingInvariant();
		si.setConstant(coeff0.numerator());
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			si.put(entry.getKey(), coeff_val.get(entry.getKey()).numerator());
		}
		
		return si;
	}
}