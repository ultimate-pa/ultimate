package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;

/**
 * This is our internal representation of a Horn clause.
 * A Horn clause consists of
 *  - a body with
 *    -- n uninterpreted predicate symbols (n >= 0)
 *    -- a transition formula
 *  - a head with
 *    either
 *     -- an uninterpreted predicate symbol
 *    or
 *     -- false
 *  - a mapping that assigns each of the argument positions of the uninterpreted predicate
 *     a free variable in the transition formula
 *     
 * Note that the uninterpreted predicate symbols may only have an arity and a name.
 * If in the formula there was a complex expression in one of the arguments of the corresponding
 * atom, this has to be encoded into the transition formula.
 * 
 * @author alex
 *
 */
public class HornClause {
	
	
	/**
	 * Stores for 
	 *  each predicate symbol in the body and, 
	 *   every argument position of the represented atom,
	 *    which TermVariable in the transition formula represents that argument in the represented atom.
	 */
	Map<HornClausePredicateSymbol, ArrayList<TermVariable>> mBodyPredToTermVariables;
	
	/**
	 * Stores for 
	 *  the predicate symbol in the head at 
	 *   every argument position of the represented atom,
	 *    which TermVariable in the transition formula represents that argument in the represented atom.
	 */
	ArrayList<TermVariable> mHeadPredTermVariables;
	HornClausePredicateSymbol mHeadPredicate;
	
	HCTransFormula mTransitionFormula;
	
	public HCTransFormula getTransitionFormula() {
		return mTransitionFormula;
	}
	
	public HornClausePredicateSymbol getHeadPredicate() {
		return mHeadPredicate;
	}
	
	public Set<HornClausePredicateSymbol> getTailPredicates() {
		return mBodyPredToTermVariables.keySet();
	}
	
	public HornClause(Term transitionFormula, ArrayList<TermVariable> bodyVars, HornClausePredicateSymbol body, Map<HornClausePredicateSymbol, ArrayList<TermVariable>> cobody) {
		mHeadPredTermVariables = bodyVars;
		mHeadPredicate = body;
		mBodyPredToTermVariables = cobody;
		
		final Map<IProgramVar, TermVariable> outVars = new HashMap<>();
		for (int i = 0; i < bodyVars.size(); ++i) {
			outVars.put(new HCVar(body, i, bodyVars.get(i)), bodyVars.get(i));
		}

		final Map<IProgramVar, TermVariable> inVars = new HashMap<>();
		for (final HornClausePredicateSymbol pred : cobody.keySet()) {
			final ArrayList<TermVariable> vars = cobody.get(pred);

			for (int i = 0; i < vars.size(); ++i) {
				inVars.put(new HCVar(pred, i, vars.get(i)), vars.get(i));
			}

		}
		
		mTransitionFormula = new HCTransFormula(transitionFormula, inVars, outVars);
	}
	
	@Override
	public String toString() {
		String cobody = "";
		
		for (final HornClausePredicateSymbol symbol : mBodyPredToTermVariables.keySet()) {
			cobody += " " + symbol.toString() + mBodyPredToTermVariables.get(symbol);
		}
		if (cobody.length() > 0) {
			cobody = "and" + cobody;
		} else {
			cobody = "true";
		}
		
		final String body = mHeadPredicate.toString() + mHeadPredTermVariables;
		
		return String.format("(%s) ^^ (%s) ~~> (%s) || in : %s || out : %s ", cobody, mTransitionFormula, body, mTransitionFormula.getInVars(), mTransitionFormula.getOutVars());
	}
}
 