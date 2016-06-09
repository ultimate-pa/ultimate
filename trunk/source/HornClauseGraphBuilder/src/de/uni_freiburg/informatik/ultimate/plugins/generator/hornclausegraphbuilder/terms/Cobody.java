package de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.terms;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.plugins.generator.hornclausegraphbuilder.graph.HornClausePredicateSymbol;

public class Cobody {
	Set<ApplicationTerm> transitions;
	Set<ApplicationTerm> predicates;

	public Cobody() {
		predicates = new HashSet<>();
		transitions = new HashSet<>();
	}
	/*
	 * public String toString() { String res = ""; if (literals.size() > 1) {
	 * boolean first = true; for (ApplicationTerm literal : literals) { res +=
	 * literal.toString(); if (!first) { res += ", "; } first = false; } } if
	 * (literals.size() == 1) { res = literals.iterator().next().toString(); }
	 * if (literals.isEmpty()) { res = "true"; } return "(" + res + ")"; }
	 * 
	 * public void addPredicates(Collection<ApplicationTerm> literals) { for
	 * (ApplicationTerm literal : literals) { addPredicate(literal); } }
	 */

	public void addPredicate(ApplicationTerm literal) {
		predicates.add(literal);
	}

	public void addTransitionFormula(ApplicationTerm formula) {
		transitions.add(formula);
	}

	public void mergeCobody(Cobody cobody) {
		for (ApplicationTerm predicate : cobody.predicates) {
			addPredicate(predicate);
		}
		for (ApplicationTerm transition : cobody.transitions) {
			addTransitionFormula(transition);
		}
	}

	private HornClausePredicateSymbol getHornPredicateSymbol(FunctionSymbol func,
			Map<String, HornClausePredicateSymbol> predicateSymbols) {
		if (!predicateSymbols.containsKey(func.getName())) {
			predicateSymbols.put(func.getName(),
					new HornClausePredicateSymbol(func.getName(), func.getParameterCount()));
		}
		return predicateSymbols.get(func.getName());
	}

	public Term getTransitionFormula(Theory theory) {
		ArrayList<Term> terms = new ArrayList<>();
		for (Term literal : transitions) {
			terms.add(literal);
		}
		if (terms.size() > 0)
			return theory.and(terms.toArray(new Term[] {}));
		else
			return theory.mTrue;
	}

	public Map<HornClausePredicateSymbol, ArrayList<TermVariable>> getPredicateToVars(
			Map<String, HornClausePredicateSymbol> predicateSymbols) {

		HashMap<HornClausePredicateSymbol, ArrayList<TermVariable>> res = new HashMap<>();
		for (ApplicationTerm predicate : predicates) {
			ArrayList<TermVariable> vars = new ArrayList<TermVariable>();
			for (Term par : predicate.getParameters()) {
				vars.add((TermVariable) par);
			}

			res.put(getHornPredicateSymbol(predicate.getFunction(), predicateSymbols), vars);
		}
		return res;
	}

	public String toString() {
		String res = "";
		boolean first = true;
		for (ApplicationTerm t : predicates) {
			if (!first) {
				res += " && ";
			}
			res += t.toString();
			first = false;
		}
		for (ApplicationTerm t : transitions) {
			if (!first) {
				res += " && ";
			}
			res += t.toString();
			first = false;
		}
		return '(' + res + ')';
	}
}
