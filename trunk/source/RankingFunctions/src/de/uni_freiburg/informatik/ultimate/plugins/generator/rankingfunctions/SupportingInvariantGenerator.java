package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Valuation;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;


/**
 * Creates and extracts supporting invariants.
 * This class is the counterpart of the RankingTemplate classes for supporting
 * invariants.
 * 
 * @author Jan Leike
 */
public class SupportingInvariantGenerator extends InstanceCounting {
	
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private static final String s_prefix = "si_";
	private static final String s_const  = "si0_";
	private static final String s_notNonDecreasingCoeff = "siD_";
	
	private Script m_script;
	
	private Term m_constant;
	private Map<BoogieVar, Term> m_coefficients;
	private Term m_notNonDecreasingCoefficient;
	
	/**
	 * @param script The SMTLib script
	 * @param variables A collection of all variables that are relevant for
	 *                   the supporting invariant
	 * @param notNonDecreasing Whether the supporting invariant has to be
	 *                         non-decreasing. (Enabling this requires a
	 *                         non-linear solver!)
	 */
	SupportingInvariantGenerator(Script script,
			Collection<BoogieVar> variables) {
		m_script = script;
		
		// Create variables
		m_constant = AuxiliaryMethods.newRealConstant(m_script,
				s_const + m_instance);
		m_coefficients = new HashMap<BoogieVar, Term>();
		for (BoogieVar var : variables) {
			m_coefficients.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix + m_instance + "_" + var.getIdentifier()));
		}
		if (Preferences.not_nondecreasing) {
			m_notNonDecreasingCoefficient =
					AuxiliaryMethods.newRealConstant(m_script,
							s_notNonDecreasingCoeff + m_instance);
			Term t = m_script.term(">=",
					m_notNonDecreasingCoefficient, m_script.decimal("0"));
			s_Logger.debug(t);
			m_script.assertTerm(t);
		}
	}
	
	/**
	 * Set the right hand side of
	 * stem(x, x0) -> si(x) >= 0
	 * to a Farkas' Lemma application
	 */
	public void setStemEntailment(FarkasApplication farkas,
			Map<BoogieVar, TermVariable> outVars) {
		Map<TermVariable, Term> stem_entail = new HashMap<TermVariable, Term>();
		for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
			stem_entail.put(entry.getValue(),
					m_script.term("-", m_coefficients.get(entry.getKey())));
		}
		farkas.entailed = stem_entail;
		farkas.gamma = m_constant;
	}
	
	/**
	 * Set the right hand side of
	 * loop(x, x') -> si(x') >= si(x)
	 * to a Farkas' Lemma application
	 */
	public void setSINonDecreasing(FarkasApplication farkas,
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		Map<TermVariable, Term> loop_entail = new HashMap<TermVariable, Term>();
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (!outVars.containsValue(entry.getValue()) &&
					m_coefficients.containsKey(entry.getKey())) {
				Term coefficient = m_coefficients.get(entry.getKey());
				if (Preferences.not_nondecreasing) {
					coefficient = m_script.term("*",
							m_notNonDecreasingCoefficient, coefficient);	
				}
				loop_entail.put(entry.getValue(), coefficient);
			}
		}
		for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
			if (!inVars.containsValue(entry.getValue()) &&
					m_coefficients.containsKey(entry.getKey())) {
				loop_entail.put(entry.getValue(), m_script.term("-", 
										m_coefficients.get(entry.getKey())));
			}
		}
		farkas.entailed = loop_entail;
		if (Preferences.not_nondecreasing) {
			Term t1 = m_script.term("*", m_notNonDecreasingCoefficient,
					m_constant);
			farkas.gamma = m_script.term("-", m_constant, t1);
		} else {
			farkas.gamma = m_script.decimal("0");
		}
	}
	
	/**
	 * Add si(x) >= 0 to the right hand side of
	 * loop(x, x') -> (template formula \/ si(x) < 0)
	 * to a Farkas' Lemma application
	 */
	public void addSI(FarkasApplication farkas,
			Map<BoogieVar, TermVariable> inVars) {
		if (farkas.gamma == null) {
			farkas.gamma = m_script.decimal("0");
		}
		if (farkas.entailed == null) {
			farkas.entailed = new HashMap<TermVariable, Term>();
		}
		farkas.gamma = m_script.term("-", farkas.gamma, m_constant);
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (m_coefficients.containsKey(entry.getKey())) {
				farkas.addToEntailed(entry.getValue(),
						m_coefficients.get(entry.getKey()));
			}
		}
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
	public SupportingInvariant extractSupportingInvariant(Valuation val)
			throws SMTLIBException {
		// Extract coefficients from the model and convert them to Rational
		Rational coeff0 = AuxiliaryMethods.const2Rational(val.get(m_constant));
		Rational gcd = Rational.ONE.gcd(coeff0);
		Map<BoogieVar, Rational> coeff_val = new HashMap<BoogieVar, Rational>();
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			Rational coeff = AuxiliaryMethods.const2Rational(
					val.get(entry.getValue()));
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
