package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.script;

import java.util.ArrayList;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.graph.HornClausePredicateSymbol;

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
	
	Term mTransitionFormula;
	
	public HornClause(Term transitionFormula, ArrayList<TermVariable> bodyVars, HornClausePredicateSymbol body, Map<HornClausePredicateSymbol, ArrayList<TermVariable>> cobody) {
		mTransitionFormula = transitionFormula;
		mHeadPredTermVariables = bodyVars;
		mHeadPredicate = body;	
		mBodyPredToTermVariables = cobody;
	}
	
	public String toString() {
		String cobody = "";
		
		for (HornClausePredicateSymbol symbol : mBodyPredToTermVariables.keySet()) {
			cobody += " " + symbol.toString() + mBodyPredToTermVariables.get(symbol);
		}
		if (cobody.length() > 0)
			cobody = "and" + cobody;
		else
			cobody = "true";
		
		String body = mHeadPredicate.toString() + mHeadPredTermVariables;
		
		return String.format("(%s) ^^ (%s) ~~> (%s)", cobody, mTransitionFormula, body);
	}
}
 