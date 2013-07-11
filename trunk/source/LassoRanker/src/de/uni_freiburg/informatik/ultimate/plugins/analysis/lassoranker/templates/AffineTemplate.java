package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates;

import java.util.*;
import java.util.Map.Entry;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxiliaryMethods;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * The linear template finds affine-linear ranking functions of the form
 * f(x) = c^T * x + c_0
 * 
 * @author Jan Leike
 *
 */
public class AffineTemplate extends RankingFunctionTemplate {
	
	private static final String s_name_delta = "delta";
	private static final String s_name_function = "rank";
	
	private Term m_delta;
	private Term m_constant;
	private Map<BoogieVar, Term> m_coefficients;
	
	public AffineTemplate(Script script, Set<BoogieVar> variables) {
		super(script, variables);
		m_delta = RankingFunctionTemplate.newDelta(script, s_name_delta);
		m_coefficients = new HashMap<BoogieVar, Term>();
		m_constant = RankingFunctionTemplate.newAffineFunction(script,
				s_name_function, variables, m_coefficients);
	}
	
	@Override
	public Collection<Term> getVariables() {
		Collection<Term> vars = new ArrayList<Term>();
		vars.addAll(m_coefficients.values());
		vars.add(m_constant);
		return vars;
	}
	
	@Override
	public RankingFunction extractRankingFunction(Map<Term, Rational> val)
			throws SMTLIBException {
		// Extract coefficients from the model and convert them to Rational
		Map<BoogieVar, Rational> coeff_val =
				new HashMap<BoogieVar, Rational>();
		Rational coeff0 = AuxiliaryMethods.const2Rational(val.get(m_constant));
		Rational gcd = Rational.ONE.gcd(coeff0);
		for (Map.Entry<BoogieVar, Term> entry : m_coefficients.entrySet()) {
			Rational coeff = val.get(entry.getValue());
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
	public Collection<Collection<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		// TODO
		return null;
	}
}