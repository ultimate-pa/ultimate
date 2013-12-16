package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.nontermination;

import java.util.*;
import java.util.Map.Entry;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.Model;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.UtilExperimental;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxiliaryMethods;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.InstanceCounting;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
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
 * Eventually this should probably go into its own ULTIMATE plugin.
 * 
 * @author Jan Leike
 */
public class NonTermination extends InstanceCounting {
	private static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	private static final String s_prefix_start = "start_"; // x0
	private static final String s_prefix_end = "end_";     // x0'
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
	private List<List<LinearInequality>> m_stem;
	private List<List<LinearInequality>> m_loop;
	
	/**
	 * Contains the NonTerminationArgument object after successful discovery
	 */
	private NonTerminationArgument m_argument = null;
	
	public NonTermination(boolean non_decreasing, Script script,
			List<List<LinearInequality>> stem,
			List<List<LinearInequality>> loop,
			TransFormula stem_transition,
			TransFormula loop_transition) {
		m_non_decreasing = non_decreasing;
		m_script = script;
		m_stem = stem;
		m_loop = loop;
		m_stem_transition = stem_transition;
		m_loop_transition = loop_transition;
	}
	
	
	public boolean checkForNonTermination() {
		// Collect variables
		Collection<TermVariable> vars = new HashSet<TermVariable>();
		for (List<LinearInequality> stem_conj : m_stem) {
			for (LinearInequality ieq : stem_conj) {
				vars.addAll(ieq.getVariables());
			}
		}
		for (List<LinearInequality> loop_conj : m_loop) {
			for (LinearInequality ieq : loop_conj) {
				vars.addAll(ieq.getVariables());
			}
		}
		
		// Create new variables
		Map<BoogieVar, Term> vars_start = new HashMap<BoogieVar, Term>();
		Map<BoogieVar, Term> vars_end = new HashMap<BoogieVar, Term>();
		Map<BoogieVar, Term> vars_ray = new HashMap<BoogieVar, Term>();
		for (BoogieVar var : m_stem_transition.getAssignedVars()) {
			vars_start.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_start + var.getIdentifier()));
			vars_end.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_end + var.getIdentifier()));
			vars_ray.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_ray + var.getIdentifier()));
		}
		for (BoogieVar var : m_loop_transition.getAssignedVars()) {
			vars_start.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_start + var.getIdentifier()));
			vars_end.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_end + var.getIdentifier()));
			vars_ray.put(var, AuxiliaryMethods.newRealConstant(m_script,
					s_prefix_ray + var.getIdentifier()));
		}
		Term lambda = AuxiliaryMethods.newRealConstant(m_script, s_lambda_name);
		
		// A_stem * (x0, x0') <= b_stem
		Term t = this.generateConstraint(m_stem_transition, m_stem, vars_start,
				vars_end, false);
		s_Logger.debug(t);
		m_script.assertTerm(t);
		
		// A_loop * (x0', x0' + y) <= b_loop
		Map<BoogieVar, Term> vars_end_plus_ray = new HashMap<BoogieVar, Term>();
		vars_end_plus_ray.putAll(vars_end);
		for (Entry<BoogieVar, Term> entry : vars_ray.entrySet()) {
			if (vars_end_plus_ray.containsKey(entry.getKey())) {
				vars_end_plus_ray.put(entry.getKey(),
						m_script.term("+",
								vars_end_plus_ray.get(entry.getKey()),
								entry.getValue()));
			} else {
				vars_end_plus_ray.put(entry.getKey(), entry.getValue());
			}
		}
		t = this.generateConstraint(m_loop_transition, m_loop, vars_end,
				vars_end_plus_ray, false);
		s_Logger.debug(t);
		m_script.assertTerm(t);
		
		// A_loop * (y, lambda * y) <= 0
		if (!m_non_decreasing) {
			Map<BoogieVar, Term> vars_ray_times_lambda =
					new HashMap<BoogieVar, Term>();
			for (Entry<BoogieVar, Term> entry : vars_ray.entrySet()) {
				vars_ray_times_lambda.put(entry.getKey(),
						m_script.term("*", entry.getValue(), lambda));
			}
			t = this.generateConstraint(m_loop_transition, m_loop, vars_ray,
					vars_ray_times_lambda, true);
		} else {
			t = this.generateConstraint(m_loop_transition, m_loop, vars_ray,
					vars_ray, true);
		}
		s_Logger.debug(t);
		m_script.assertTerm(t);
		
		// Check for satisfiability
		boolean success = false;
		if (m_script.checkSat() == LBool.SAT) {
			success = true;
			m_argument = extractArgument(vars_start, vars_end, vars_ray);
		}
		
		return success;
	}
	
	private Term generateConstraint(TransFormula trans_formula,
			List<List<LinearInequality>> trans_ieqs,
			Map<BoogieVar, Term> varsIn,
			Map<BoogieVar, Term> varsOut,
			boolean rays) {
		Term[] disjunction = new Term[trans_ieqs.size()];
		int i = 0;
		for (List<LinearInequality> trans_conj : trans_ieqs) {
			Term[] conjunction = new Term[trans_conj.size()];
			int j = 0;
			for (LinearInequality ieq : trans_conj) {
				List<Term> summands = new ArrayList<Term>();
				Collection<TermVariable> added_vars = new HashSet<TermVariable>();
				
				// inVars
				for (Entry<BoogieVar, TermVariable> entry :
						trans_formula.getInVars().entrySet()) {
					if (trans_formula.getOutVars().containsValue(entry.getValue())) {
						continue;
					}
					summands.add(m_script.term("*", varsIn.get(entry.getKey()),
							ieq.getCoefficient(entry.getValue()).asTerm(m_script)));
					added_vars.add(entry.getValue());
				}
				
				// outVars
				for (Entry<BoogieVar, TermVariable> entry :
						trans_formula.getOutVars().entrySet()) {
					assert(!added_vars.contains(entry.getValue()));
					if (!varsOut.containsKey(entry.getKey())) {
						continue;
					}
					summands.add(m_script.term("*", varsOut.get(entry.getKey()),
						ieq.getCoefficient(entry.getValue()).asTerm(m_script)));
					added_vars.add(entry.getValue());
				}
				
				// tmpVars
				Set<TermVariable> all_vars = new HashSet<TermVariable>(ieq.getVariables());
				all_vars.removeAll(added_vars);
				for (TermVariable var : all_vars) {
					summands.add(m_script.term("*",
							AuxiliaryMethods.newRealConstant(m_script,
									s_prefix_aux + m_aux_counter),
							ieq.getCoefficient(var).asTerm(m_script)
					));
					++m_aux_counter;
				}
				if (!rays) {
					summands.add(ieq.getConstant().asTerm(m_script));
				}
				conjunction[j] = m_script.term(ieq.getInequalitySymbol(),
						UtilExperimental.sum(m_script, m_script.sort("Real"),
								summands.toArray(new Term[0])),
						m_script.decimal("0"));
				++j;
			}
			disjunction[i] = Util.and(m_script, conjunction);
			++i;
		}
		return Util.or(m_script, disjunction);
	}
	
	/**
	 * Extract the non-termination argument from a satisfiable script
	 * @return
	 * @throws SMTLIBException
	 */
	private NonTerminationArgument extractArgument(
			Map<BoogieVar, Term> vars_start,
			Map<BoogieVar, Term> vars_end,
			Map<BoogieVar, Term> vars_ray)
			throws SMTLIBException {
		assert m_script.checkSat() == LBool.SAT;
		
//		Model model = m_script.getModel();
		
		// TODO
		
		return null;
	}
	
	/**
	 * @return the non-termination argument discovered
	 */
	public NonTerminationArgument getArgument() {
		return m_argument;
	}
}
