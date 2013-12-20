package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.*;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.exceptions.TermException;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.TransFormula;


/**
 * The non-termination template checks for non-termination.
 * 
 * We check the following constraints.
 * <pre>
 * exists x0, x0', y
 *    A_stem * (x0, x0') <= b_stem
 * /\ A_loop * (x0', x0' + y) <= b_loop
 * /\ A_loop * (y, lambda * y) <= 0
 * </pre>
 * 
 * This class can't be a RankingFunctionsTemplate because that class
 * makes a bunch of assumptions regarding how the constraints are generated,
 * including the mandatory use of Motzkin's Theorem.
 * 
 * @author Jan Leike
 */
public class NonTerminationArgumentSynthesizer {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private static final String s_prefix_init = "init_";   // x0
	private static final String s_prefix_honda = "honda_"; // x0'
	private static final String s_prefix_ray = "ray_";     // y
	private static final String s_prefix_aux = "aux_";
	private static final String s_lambda_name = "lambda";  // lambda
	
	/**
	 * Counter for auxiliary variables
	 */
	public static long m_aux_counter = 0;
	
	/**
	 * Is the ray non-decreasing?
	 */
	private boolean m_non_decreasing;
	
	/**
	 * SMT script for the template instance
	 */
	private Script m_script;
	
	// Stem and loop transitions for the linear lasso program
	private TransFormula m_stem_transition;
	private TransFormula m_loop_transition;
	
	// Stem and loop transitions as linear inequalities in DNF
	private LinearTransition m_stem;
	private LinearTransition m_loop;
	
	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private NonTerminationArgument m_argument = null;
	
	public NonTerminationArgumentSynthesizer(boolean non_decreasing, Script script,
			LinearTransition stem,
			LinearTransition loop,
			TransFormula stem_transition,
			TransFormula loop_transition) {
		m_non_decreasing = non_decreasing;
		m_script = script;
		m_stem = stem;
		m_loop = loop;
		m_stem_transition = stem_transition;
		m_loop_transition = loop_transition;
	}
	
	
	/**
	 * @return all BoogieVars that occur in the program
	 */
	private Collection<BoogieVar> getBoogieVars() {
		Collection<BoogieVar> boogieVars = new HashSet<BoogieVar>();
		boogieVars.addAll(m_stem_transition.getAssignedVars());
		boogieVars.addAll(m_stem_transition.getInVars().keySet());
		boogieVars.addAll(m_stem_transition.getOutVars().keySet());
		boogieVars.addAll(m_loop_transition.getAssignedVars());
		boogieVars.addAll(m_loop_transition.getInVars().keySet());
		boogieVars.addAll(m_loop_transition.getOutVars().keySet());
		return boogieVars;
	}
	
	/**
	 * @return whether nontermination has been proven
	 */
	public boolean checkForNonTermination() {
		// Create new variables
		Map<BoogieVar, Term> vars_init = new HashMap<BoogieVar, Term>();
		Map<BoogieVar, Term> vars_honda = new HashMap<BoogieVar, Term>();
		Map<BoogieVar, Term> vars_ray = new HashMap<BoogieVar, Term>();
		for (BoogieVar var : getBoogieVars()) {
			vars_init.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_init + var.getIdentifier()));
			vars_honda.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_honda + var.getIdentifier()));
			vars_ray.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_ray + var.getIdentifier()));
		}
		Term lambda = AuxiliaryMethods.newRealConstant(m_script, s_lambda_name);
		
		Term constraints = generateConstraints(vars_init, vars_honda, vars_ray,
				lambda);
		s_Logger.debug(SMTPrettyPrinter.print(constraints));
		m_script.assertTerm(constraints);
		
		// Check for satisfiability
		boolean success = false;
		if (m_script.checkSat() == LBool.SAT) {
			success = true;
			m_argument = extractArgument(vars_init, vars_honda, vars_ray,
					lambda);
		}
		
		return success;
	}
	
	/**
	 * Generate the constraints corresponding to the nontermination argument
	 * @param vars_init 
	 * @param vars_honda
	 * @param vars_ray
	 * @param lambda
	 * @return
	 */
	public Term generateConstraints(Map<BoogieVar, Term> vars_init,
			Map<BoogieVar, Term> vars_honda, Map<BoogieVar, Term> vars_ray,
			Term lambda) {
		Collection<BoogieVar> boogieVars = getBoogieVars();
		
		// lambda >= 0
		Term t0 = m_script.term(">=", lambda, m_script.decimal("0"));
		
		// A_stem * (x0, x0') <= b_stem
		Term t1 = this.generateConstraint(m_stem_transition, m_stem, vars_init,
				vars_honda, false);
		
		// A_loop * (x0', x0' + y) <= b_loop
		Map<BoogieVar, Term> vars_end_plus_ray = new HashMap<BoogieVar, Term>();
		vars_end_plus_ray.putAll(vars_honda);
		for (BoogieVar bv : boogieVars) {
			vars_end_plus_ray.put(bv, m_script.term("+", vars_honda.get(bv),
					vars_ray.get(bv)));
		}
		Term t2 = this.generateConstraint(m_loop_transition, m_loop, vars_honda,
				vars_end_plus_ray, false);
		
		// A_loop * (y, lambda * y) <= 0
		Term t3;
		if (!m_non_decreasing) {
			Map<BoogieVar, Term> vars_ray_times_lambda =
					new HashMap<BoogieVar, Term>();
			for (BoogieVar bv : boogieVars) {
				vars_ray_times_lambda.put(bv,
						m_script.term("*", vars_ray.get(bv), lambda));
			}
			t3 = this.generateConstraint(m_loop_transition, m_loop, vars_ray,
					vars_ray_times_lambda, true);
		} else {
			t3 = this.generateConstraint(m_loop_transition, m_loop, vars_ray,
					vars_ray, true);
		}
		return m_script.term("and", t0, t1, t2, t3);
	}
	
	private Term generateConstraint(TransFormula trans_formula,
			LinearTransition linear_transition,
			Map<BoogieVar, Term> varsIn,
			Map<BoogieVar, Term> varsOut,
			boolean rays) {
		Map<TermVariable, Term> auxVars = new HashMap<TermVariable, Term>();
		Term[] disjunction = new Term[linear_transition.getNumPolyhedra()];
		int i = 0;
		for (List<LinearInequality> trans_conj
				: linear_transition.getPolyhedra()) {
			List<Term> conjunction = new ArrayList<Term>(trans_conj.size());
			for (LinearInequality ieq : trans_conj) {
				List<Term> summands = new ArrayList<Term>();
				Collection<TermVariable> added_vars = new HashSet<TermVariable>();
				
				// outVars
				for (Entry<BoogieVar, TermVariable> entry :
						trans_formula.getOutVars().entrySet()) {
					if (!varsOut.containsKey(entry.getKey())) {
						continue;
					}
					summands.add(m_script.term("*", varsOut.get(entry.getKey()),
						ieq.getCoefficient(entry.getValue()).asTerm(m_script)));
					added_vars.add(entry.getValue());
				}
				
				// inVars
				for (Entry<BoogieVar, TermVariable> entry :
						trans_formula.getInVars().entrySet()) {
					if (added_vars.contains(entry.getValue())) {
						// the transition implicitly requires that
						// entry.getKey() is constant
						conjunction.add(m_script.term(
								"=",
								varsIn.get(entry.getKey()),
								varsOut.get(entry.getKey())
						));
						continue;
					}
					summands.add(m_script.term("*", varsIn.get(entry.getKey()),
							ieq.getCoefficient(
									entry.getValue()).asTerm(m_script)));
					added_vars.add(entry.getValue());
				}
				
				// tmpVars
				Set<TermVariable> all_vars =
						new HashSet<TermVariable>(ieq.getVariables());
				all_vars.removeAll(added_vars);
				for (TermVariable var : all_vars) {
					Term v;
					if (auxVars.containsKey(var)) {
						v = auxVars.get(var);
					} else {
						v = AuxiliaryMethods.newRealConstant(m_script,
								s_prefix_aux + m_aux_counter);
						auxVars.put(var, v);
					}
					summands.add(m_script.term("*", v,
							ieq.getCoefficient(var).asTerm(m_script)
					));
					++m_aux_counter;
				}
				if (!rays) {
					summands.add(ieq.getConstant().asTerm(m_script));
				}
				conjunction.add(m_script.term(ieq.getInequalitySymbol(),
						UtilExperimental.sum(m_script, m_script.sort("Real"),
								summands.toArray(new Term[0])),
						m_script.decimal("0")));
			}
			disjunction[i] = Util.and(m_script,
					conjunction.toArray(new Term[0]));
			++i;
		}
		return Util.or(m_script, disjunction);
	}
	
	/**
	 * Extract a program state from the SMT script's model
	 * 
	 * @param vars a map from the program variables to corresponding SMT
	 *             variables
	 * @return the program state as a map from program variables to rational
	 *         numbers
	 */
	private Map<BoogieVar, Rational> extractState(Map<BoogieVar, Term> vars)
			throws SMTLIBException, UnsupportedOperationException,
			TermException {
		if (vars.isEmpty()) {
			return Collections.emptyMap();
		}
		assert(m_script.checkSat() == LBool.SAT);
		Map<Term, Rational> val = AuxiliaryMethods.preprocessValuation(
				m_script.getValue(vars.values().toArray(new Term[0])));
		// Concatenate vars and val
		Map<BoogieVar, Rational> state = new HashMap<BoogieVar, Rational>();
		for (Entry<BoogieVar, Term> entry : vars.entrySet()) {
			assert(val.containsKey(entry.getValue()));
			state.put(entry.getKey(), val.get(entry.getValue()));
		}
		return state;
	}
	
	/**
	 * Extract the non-termination argument from a satisfiable script
	 * @return
	 * @throws SMTLIBException
	 */
	private NonTerminationArgument extractArgument(
			Map<BoogieVar, Term> vars_init,
			Map<BoogieVar, Term> vars_honda,
			Map<BoogieVar, Term> vars_ray,
			Term var_lambda) {
		assert m_script.checkSat() == LBool.SAT;
		
		try {
			Map<BoogieVar, Rational> state0 = extractState(vars_init);
			Map<BoogieVar, Rational> state1 = extractState(vars_honda);
			Map<BoogieVar, Rational> ray = extractState(vars_ray);
			Rational lambda = AuxiliaryMethods.const2Rational(
					m_script.getValue(new Term[] {var_lambda}).get(var_lambda));
			return new NonTerminationArgument(state0, state1, ray, lambda);
		} catch (UnsupportedOperationException e) {
			// do nothing
		} catch (TermException e) {
			// do nothing
		}
		return null;
	}
	
	/**
	 * @return the non-termination argument discovered
	 */
	public NonTerminationArgument getArgument() {
		return m_argument;
	}
}
