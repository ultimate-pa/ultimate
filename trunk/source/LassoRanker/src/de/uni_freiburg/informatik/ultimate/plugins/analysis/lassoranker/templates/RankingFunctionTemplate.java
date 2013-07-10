package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.templates;

import java.util.*;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Activator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.MotzkinTransformation;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.rankingfunctions.RankingFunction;


/**
 * This is the superclass for templates for linear ranking. All templates will
 * derive from this class.
 * 
 * @author Jan Leike
 *
 */
public abstract class RankingFunctionTemplate {
	
	protected static Logger s_Logger =
			UltimateServices.getInstance().getLogger(Activator.s_PLUGIN_ID);
	
	protected Script m_script;
	protected Collection<BoogieVar> m_variables;
	
	/**
	 * Ranking template constructor
	 * WARNING: the subclasses MUST contain a constructor of this type!
	 * @param script The SMTLib script
	 * @param variables A collection of all variables that are relevant for
	 *                   ranking
	 */
	RankingFunctionTemplate(Script script, Set<BoogieVar> variables) {
		m_script = script;
		m_variables = variables;
	}
	
	/**
	 * Show the underlying formula used for this template instance
	 */
	public abstract String toString();
	
	/**
	 * Return a text corresponding to the template generated in this instance
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 */
	public abstract String getDetails(Map<BoogieVar, TermVariable> inVars,
			Map<BoogieVar, TermVariable> outVars);
	
	/**
	 * Generate the Farkas' Lemma applications for this template
	 * 
	 * @param inVars  Input variables for the loop transition
	 * @param outVars Output variables for the loop transition
	 * @return FarkasApplications in CNF; one clause for every conjunct in this
	 *          template's formula. These Applictions will be augmented by
	 *          the loop transition in form of affine terms and the supporting
	 *          invariants.
	 */
	public abstract Collection<Collection<MotzkinTransformation>> generateFarkas(
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
	public abstract RankingFunction extractRankingFunction(Map<Term, Term> val)
			throws SMTLIBException;
	
	/**
	 * Workaround by Matthias: Returns all deltas of the template. You want to
	 * assert delta > 0 for each of these.
	 */
	public abstract List<Term> getDeltas();
}
