package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.AuxiliaryMethods;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.FarkasApplication;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;


/**
 * The linear template finds affine linear ranking functions of the form
 * f(x) = c^T * x + c_0.
 * 
 * @author Jan Leike
 *
 */
public class LinearTemplate extends RankingTemplate {
	
	private static final String s_name_delta = "delta";
	private static final String s_name_constant = "rank0";
	private static final String s_prefix_coefficients = "rank_";
	
	private Term m_delta;
	private Term m_constant;
	private Map<BoogieVar, Term> m_coefficients;
	
	public LinearTemplate(Script script, Set<BoogieVar> variables) {
		super(script, variables);
		
		// Create variables
		m_delta = AuxiliaryMethods.newRealConstant(m_script, s_name_delta);
		Term t = m_script.term(">", m_delta, m_script.decimal("0"));
		s_Logger.debug(t);
		m_script.assertTerm(t);
		
		m_constant = AuxiliaryMethods.newRealConstant(m_script,
				s_name_constant);
		m_coefficients = new HashMap<BoogieVar, Term>();
		for (BoogieVar var : variables) {
			m_coefficients.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_coefficients + var.getIdentifier()));
		}
	}
	
	@Override
	public Collection<Term> getVariables() {
		Collection<Term> vars = new ArrayList<Term>();
		vars.addAll(m_coefficients.values());
		vars.add(m_constant);
		return vars;
	}
	
	@Override
	public RankingFunction extractRankingFunction(Map<Term, Term> val)
			throws SMTLIBException {
		// Extract coefficients from the model and convert them to Rational
		Map<BoogieVar, Rational> coeff_val =
				new HashMap<BoogieVar, Rational>();
		Rational coeff0 = AuxiliaryMethods.const2Rational(val.get(m_constant));
		Rational gcd = Rational.ONE.gcd(coeff0);
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			Rational coeff = AuxiliaryMethods.const2Rational(
					val.get(entry.getValue()));
			coeff_val.put(entry.getKey(), coeff);
			gcd = coeff.gcd(gcd);
		}
		
		// Multiply all coefficients with the greatest common denominator
		// Note: Any multiple of a ranking function is also a ranking function.
		coeff0 = coeff0.div(gcd);
		for (Map.Entry<BoogieVar, Rational> entry : coeff_val.entrySet()) {
			assert(entry.getValue().div(gcd).denominator().equals(
					BigInteger.ONE));
			coeff_val.put(entry.getKey(), entry.getValue().div(gcd));
		}
		
		// Construct the ranking function object
		LinearRankingFunction rf = new LinearRankingFunction();
		rf.setConstant(coeff0.numerator());
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			rf.put(entry.getKey(), coeff_val.get(entry.getKey()).numerator());
		}
		
		return rf;
	}
	
	@Override
	public Collection<Collection<FarkasApplication>> generateFarkas(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		Collection<FarkasApplication> conj = new ArrayList<FarkasApplication>();
		
		// f(x) >= 0
		FarkasApplication farkas = new FarkasApplication(m_script);
		farkas.wantsSI = Preferences.supporting_invariant_for_lower_bound;
		farkas.gamma = m_constant;
		farkas.ieqsymb = FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
		farkas.entailed = new HashMap<TermVariable, Term>();
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (m_coefficients.containsKey(entry.getKey())) {
				farkas.entailed.put(entry.getValue(),
						m_script.term("-", m_coefficients.get(entry.getKey())));
			}
		}
		conj.add(farkas);
		
		// f(x) >= f(x') - delta
		farkas = new FarkasApplication(m_script);
		farkas.wantsSI = true;
		farkas.gamma = m_script.term("-", m_delta);
		farkas.ieqsymb = FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
		farkas.entailed = new HashMap<TermVariable, Term>();
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (m_coefficients.containsKey(entry.getKey())) {
				farkas.entailed.put(entry.getValue(),
						m_script.term("-", m_coefficients.get(entry.getKey())));
			}
		}
		for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
			if (inVars.containsValue(entry.getValue())) {
				farkas.entailed.remove(entry.getValue());
			} else if (m_coefficients.containsKey(entry.getKey())) {
				farkas.entailed.put(entry.getValue(),
						m_coefficients.get(entry.getKey()));
			}
		}
		conj.add(farkas);
		
		Collection<Collection<FarkasApplication>> cnf =
				new ArrayList<Collection<FarkasApplication>>();
		for (FarkasApplication atom : conj) {
			List<FarkasApplication> clause = new ArrayList<FarkasApplication>();
			clause.add(atom);
			cnf.add(clause);
		}
		return cnf;
	}
	
	@Override
	public String toString() {
		return "delta > 0 /\\ f(x) >= 0 /\\ f(x) >= f(x') + delta";
	}

	@Override
	public String getDetails(Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		String result = "delta > 0\n";
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (m_coefficients.containsKey(entry.getKey())) {
				result += m_coefficients.get(entry.getKey()) + " * ";
				result += entry.getValue() + " + ";
			}
		}
		result += m_constant + " >= 0\n";
		for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
			if (!outVars.containsValue(entry.getValue()) &&
					m_coefficients.containsKey(entry.getKey())) {
				result += m_coefficients.get(entry.getKey()) + " * ";
				result += entry.getValue() + " + ";
			}
		}
		if (!m_coefficients.isEmpty()) {
			result = result.substring(0, result.length() - 3);
		} else {
			result += "0";
		}
		result += " >= ";
		for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
			if (!inVars.containsValue(entry.getValue())
					&& m_coefficients.containsKey(entry.getKey())) {
				result += m_coefficients.get(entry.getKey()) + " * ";
				result += entry.getValue() + " + ";
			}
		}
		result += "delta";
		return result;
	}
	
	@Override
	public List<Term> getDeltas() {
		ArrayList<Term> result = new ArrayList<Term>();
		result.add(m_delta);
		return result;
	}
}
