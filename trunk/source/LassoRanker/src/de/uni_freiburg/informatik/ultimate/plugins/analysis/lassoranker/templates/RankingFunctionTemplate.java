package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxiliaryMethods;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.LinearInequality;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * This is the superclass for templates for linear ranking. All templates will
 * derive from this class.
 * 
 * @author Jan Leike
 *
 */
public abstract class RankingFunctionTemplate {
	protected Script m_script;
	protected Collection<BoogieVar> m_variables;
	
	private boolean m_initialized = false;
	
	RankingFunctionTemplate() {
		m_script = null;
		m_variables = null;
	}
	
	/**
	 * Initialize the template; call this before constaints()
	 * @param script The SMTLib script
	 * @param vars A collection of all variables that are relevant for
	 *                   ranking
	 */
	public void init(Script script, Collection<BoogieVar> vars) {
		m_script = script;
		m_variables = vars;
		m_initialized = true;
	}
	
	/**
	 * Check if the template was properly initialized using init()
	 */
	protected void checkInitialized() {
		assert(m_initialized);
		assert(m_script != null);
		assert(m_variables != null);
	}
	
	/**
	 * Generate the Farkas' Lemma applications for this template
	 * 
	 * Must be initialized before calling this!
	 * 
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 * @return FarkasApplications in CNF; one clause for every conjunct in this
	 *          template's formula. These Applictions will be augmented by
	 *          the loop transition in form of affine terms and the supporting
	 *          invariants.
	 */
	public abstract Collection<Collection<LinearInequality>> constraints(
			Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars);
	
	/**
	 * Return all SMT variables used by this template
	 */
	public abstract Collection<Term> getVariables();
	
	/**
	 * Extract the ranking function from a model
	 * @param script The SMTLib interface script
	 * @return ranking function
	 * @throws SMTLIBException
	 */
	public abstract RankingFunction extractRankingFunction(Map<Term,
			Rational> val) throws SMTLIBException;
	
	/**
	 * Create a new positive variable (as a nullary function symbol)
	 * @param script current SMT script
	 * @param name the new variable's name
	 * @return the new variable as a term
	 */
	public static Term newDelta(Script script, String name) {
		Term delta = AuxiliaryMethods.newRealConstant(script, name);
		Term t = script.term(">", delta, script.decimal("0"));
		script.assertTerm(t);
		return delta;
	}
}