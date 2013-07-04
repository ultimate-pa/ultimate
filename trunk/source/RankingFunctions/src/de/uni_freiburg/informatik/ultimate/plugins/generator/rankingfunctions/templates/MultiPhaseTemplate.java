package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.templates;

import java.math.BigInteger;
import java.util.*;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.AuxiliaryMethods;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.FarkasApplication;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.PowerList;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.LinearRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.MultiPhaseRankingFunction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions.functions.RankingFunction;


/**
 * The multi phase template finds ranking functions that have a finite number of
 * phases where each phase is of the form
 * f_i(x) = c^T * x + c_0
 * and the next phase i+1 is entered when f_i(x) < 0.
 * 
 * @author Jan Leike
 *
 */
public class MultiPhaseTemplate extends RankingTemplate {
	
	private static final String s_name_deltas = "delta_";
	private static final String s_name_constants = "rank0_";
	private static final String s_prefix_coefficients = "rank_";
	
	/**
	 * The maximum number of phases to instantiate for
	 */
	public static int maxphases = 4; 
	
	private int m_phases;
	private List<Term> m_deltas;
	private List<AffineFunction> m_functions;
	
	/**
	 * Container object holding the variables for an affine function
	 */
	private class AffineFunction {
		Term constant;
		Map<BoogieVar, Term> coefficients;
		
		AffineFunction() {
			coefficients = new HashMap<BoogieVar, Term>();
		}
	}
	
	public MultiPhaseTemplate(Script script, Set<BoogieVar> variables) {
		super(script, variables);
		
		// Number of phases to instantiate for
		m_phases = variables.size() > maxphases ? maxphases : variables.size();
		assert(m_phases >= 0);
		
		// Create variables
		m_deltas = new ArrayList<Term>();
		m_functions = new ArrayList<AffineFunction>();
		for (int i = 0; i < m_phases; ++i) {
			// New delta > 0
			Term delta = AuxiliaryMethods.newRealConstant(m_script,
					s_name_deltas + i);
			m_deltas.add(delta);
			Term t = m_script.term(">", delta, m_script.decimal("0"));
			s_Logger.debug(t);
			m_script.assertTerm(t);
			
			// Ranking function coefficients
			AffineFunction af = new AffineFunction();
			af.constant = AuxiliaryMethods.newRealConstant(m_script,
					s_name_constants + i);
			for (BoogieVar var : variables) {
				af.coefficients.put(var,
						AuxiliaryMethods.newRealConstant(m_script,
						s_prefix_coefficients + var.getIdentifier() + "_" + i));
			}
			m_functions.add(af);
		}
	}
	
	@Override
	public Collection<Term> getVariables() {
		Collection<Term> vars = new ArrayList<Term>();
//		Matthias: I commented the following line, I don't think its necessary.
//		vars.addAll(m_deltas);
		for (AffineFunction af : m_functions) {
			vars.add(af.constant);
			vars.addAll(af.coefficients.values());
		}
		return vars;
	}
	
	@Override
	public RankingFunction extractRankingFunction(Map<Term, Term> val)
			throws SMTLIBException {
		MultiPhaseRankingFunction mprf = new MultiPhaseRankingFunction();
		for (AffineFunction af : m_functions) {
			// Extract coefficients from the model and convert them to Rational
			Map<BoogieVar, Rational> coeff_val =
					new HashMap<BoogieVar, Rational>();
			Rational coeff0 = AuxiliaryMethods.const2Rational(val.get(af.constant));
			Rational gcd = Rational.ONE.gcd(coeff0);
			for (Map.Entry<BoogieVar, Term> entry : af.coefficients.entrySet()) {
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
			for (Map.Entry<BoogieVar, Term> entry : af.coefficients.entrySet()) {
				rf.put(entry.getKey(), coeff_val.get(entry.getKey()).numerator());
			}
			
			mprf.addPhase(rf);
		}
		return mprf;
	}
	
	@Override
	public Collection<Collection<FarkasApplication>> generateFarkas(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		assert(m_phases >= 0);
		Collection<Collection<FarkasApplication>> cnf =
				new ArrayList<Collection<FarkasApplication>>();
		
		// /\_i (f_i(x') < f_i(x) - delta_i \/_{j=1}^{i-1} f_j(x) >= 0)
		List<AffineFunction> partial_af_list = new ArrayList<AffineFunction>();
		for (int i = 0; i < m_functions.size(); ++i) {
			AffineFunction af = m_functions.get(i);
			
			Collection<FarkasApplication> disj =
					new ArrayList<FarkasApplication>();
			for (List<AffineFunction> functions :
				new PowerList<AffineFunction>(partial_af_list)) {
				FarkasApplication farkas = new FarkasApplication(m_script);
				farkas.wantsSI = true;
				farkas.gamma = m_script.term("-", m_deltas.get(i));
				farkas.ieqsymb = FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
				farkas.entailed = new HashMap<TermVariable, Term>();
				
				for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey()) &&
							!outVars.containsKey(entry.getValue())) {
						farkas.addToEntailed(entry.getValue(),
								m_script.term("-",
										af.coefficients.get(entry.getKey())));
					}
				}
				for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey()) &&
							!inVars.containsValue(entry.getValue())) {
						farkas.addToEntailed(entry.getValue(),
								af.coefficients.get(entry.getKey()));
					}
				}
				
				for (AffineFunction af2 : functions) {
					farkas.gamma = m_script.term("+", farkas.gamma, af.constant);
					for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
						if (af2.coefficients.containsKey(entry.getKey())) {
							farkas.addToEntailed(entry.getValue(),
									m_script.term("-",
											af2.coefficients.get(entry.getKey())));
						}
					}
				}
				disj.add(farkas);
			}
			cnf.add(disj);
			partial_af_list.add(af);
		}
		
		// \/_i f_i(x) >= 0
		Collection<FarkasApplication> disj = new ArrayList<FarkasApplication>();
		for (List<AffineFunction> functions :
			new PowerList<AffineFunction>(m_functions)) {
			if (functions.isEmpty()) {
				continue;
			}
			FarkasApplication farkas = new FarkasApplication(m_script);
			farkas.wantsSI = Preferences.supporting_invariant_for_lower_bound;
			farkas.gamma = m_script.decimal("0");
			farkas.ieqsymb = FarkasApplication.Inequality.LESS_THAN_OR_EQUAL;
			farkas.entailed = new HashMap<TermVariable, Term>();
			for (AffineFunction af : functions) {
				farkas.gamma = m_script.term("+", farkas.gamma, af.constant);
				for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey())) {
						farkas.addToEntailed(entry.getValue(),
								m_script.term("-",
										af.coefficients.get(entry.getKey())));
					}
				}
			}
			disj.add(farkas);
		}
		cnf.add(disj);
		
		return cnf;
	}
	
	@Override
	public String toString() {
		return "   /\\_i delta_i > 0\n" +
				"/\\ /\\_i (f_i(x') < f_i(x) - delta_i \\/" +
					"\\/_{j=1}^{i-1} f_j(x) >= 0)\n" +
				"/\\ \\/_i f_i(x) >= 0";
	}
	
	@Override
	public String getDetails(Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars) {
		assert(m_phases >= 0);
		String result = "";
		
		// delta_i > 0
		boolean first = true;
		for (Term delta : m_deltas) {
			if (first) {
				result += "   ";
				first = false;
			} else {
				result += "/\\ ";
			}
			result += delta.toString() + " > 0\n";
		}
		
		// /\_i (f_i(x') < f_i(x) - delta_i \/_{j=1}^{i-1} f_j(x) >= 0)
		List<AffineFunction> partial_af_list = new ArrayList<AffineFunction>();
		first = true;
		for (int i = 0; i < m_functions.size(); ++i) {
			AffineFunction af = m_functions.get(i);
			
			result += "/\\ [\n";
			boolean first2 = true;
			for (List<AffineFunction> functions :
				new PowerList<AffineFunction>(partial_af_list)) {
				if (first2) {
					result += "       ";
					first2 = false;
				} else {
					result += "    \\/ ";
				}
				boolean first3 = true;
				for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey()) &&
							!outVars.containsKey(entry.getValue())) {
						if (first3) {
							first3 = false;
						} else {
							result += " + ";
						}
						result += entry.getValue() + " * "
							+ af.coefficients.get(entry.getKey());
					}
				}
				for (Entry<BoogieVar, TermVariable> entry : outVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey()) &&
							!inVars.containsValue(entry.getValue())) {
						result += " - " + entry.getValue() + " * "
								+ af.coefficients.get(entry.getKey());
					}
				}
				
				for (AffineFunction af2 : functions) {
					for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
						if (af2.coefficients.containsKey(entry.getKey())) {
							if (first3) {
								first3 = false;
							} else {
								result += " + ";
							}
							result += entry.getValue() + " * "
									+ af2.coefficients.get(entry.getKey());
						}
					}
					result += " + " + af.constant.toString();
				}
				result += " >= " + m_deltas.get(i).toString() + "\n";
			}
			result += "]\n";
			partial_af_list.add(af);
		}
		
		// \/_i f_i(x) >= 0
		result += "/\\ [\n";
		first = true;
		for (List<AffineFunction> functions :
			new PowerList<AffineFunction>(m_functions)) {
			if (functions.isEmpty()) {
				continue;
			}
			if (first) {
				result += "       0 <= ";
				first = false;
			} else {
				result += "    \\/ 0 <= ";
			}
			boolean first2 = true;
			for (AffineFunction af : functions) {
				if (first2) {
					first2 = false;
				} else {
					result += " + ";
				}
				for (Entry<BoogieVar, TermVariable> entry : inVars.entrySet()) {
					if (af.coefficients.containsKey(entry.getKey())) {
						result += entry.getKey() + "*"
								+ af.coefficients.get(entry.getKey());
					}
					result += " + " + af.constant.toString();
				}
			}
			result += "\n";
		}
		result += "]";
		
		return result;
	}
	
	@Override
	public List<Term> getDeltas() {
		return m_deltas;
	}
}
