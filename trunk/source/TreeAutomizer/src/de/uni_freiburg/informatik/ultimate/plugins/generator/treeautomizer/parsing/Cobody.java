package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCVar;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;

public class Cobody {
	Set<Term> transitions;
	Set<ApplicationTerm> predicates;
	Map<HCVar, TermVariable> inVars;

	public Cobody() {
		predicates = new HashSet<>();
		transitions = new HashSet<>();
		inVars = new HashMap<>();
	}

	public void addPredicate(ApplicationTerm literal) {
		predicates.add(literal);
	}

	public void addTransitionFormula(Term formula) {
		transitions.add(formula);
	}

	public void mergeCobody(Cobody cobody) {
		for (final ApplicationTerm predicate : cobody.predicates) {
			addPredicate(predicate);
		}
		for (final Term transition : cobody.transitions) {
			addTransitionFormula(transition);
		}
	}
	
	public Body negate() {
		final Body res = new Body();
		res.mergeCobody(this);
		return res;
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
		if (transitions.isEmpty()) {
			return theory.mTrue;
		} else {
			return theory.and(transitions.toArray(new Term[] {}));
		}
	}

	public Map<HornClausePredicateSymbol, List<TermVariable>> getPredicateToVars(
			Map<String, HornClausePredicateSymbol> predicateSymbols) {

		final HashMap<HornClausePredicateSymbol, List<TermVariable>> res = new HashMap<>();
		for (final ApplicationTerm predicate : predicates) {
			final ArrayList<TermVariable> vars = new ArrayList<>();
			for (final Term par : predicate.getParameters()) {
				vars.add((TermVariable) par);
			}

			res.put(getHornPredicateSymbol(predicate.getFunction(), predicateSymbols), vars);
		}
		return res;
	}

	@Override
	public String toString() {
		String res = "";
		boolean first = true;
		for (final ApplicationTerm t : predicates) {
			if (!first) {
				res += " && ";
			}
			res += t.toString();
			first = false;
		}
		for (final Term t : transitions) {
			if (!first) {
				res += " && ";
			}
			res += t.toStringDirect();
			first = false;
		}
		return '(' + res + ')';
	}
}
