package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.terms;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.FunctionSymbol;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;

public class Body {
	Cobody cobody;
	ApplicationTerm head;
	
	public Body() {
		cobody = new Cobody();
	}

	public void addPredicateToCobody(ApplicationTerm literal) {
		cobody.addPredicate(literal);
	}

	public HornClause convertToHornClause(Map<String, HornClausePredicateSymbol> predicates, Theory theory) {
		final Map<HornClausePredicateSymbol, ArrayList<TermVariable>> tt = getBodyPredicateToVars(predicates);
		assert tt.size() <= 1;
		final HornClausePredicateSymbol bodySymbol = tt.keySet().iterator().hasNext() ? tt.keySet().iterator().next()
				: new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol();
		return new HornClause(getTransitionFormula(theory),
				tt.containsKey(bodySymbol) ? tt.get(bodySymbol) : new ArrayList<>(), bodySymbol,
				getCobodyPredicateToVars(predicates));

	}
	public boolean setHead(ApplicationTerm literal) {
		if (head == null) {
			head = literal;
			return true;
		} else {
			return false;
		}
	}

	public void mergeCobody(Cobody cobody) {
		this.cobody.mergeCobody(cobody);
	}

	
	public void addTransitionFormula(Term formula) {
		cobody.addTransitionFormula(formula);
	}

	@Override
	public String toString() {
		return '(' + cobody.toString() + " ==> " + (head == null ? "false" : head.toString()) + ')';
	}

	private HornClausePredicateSymbol getHornPredicateSymbol(FunctionSymbol func,
			Map<String, HornClausePredicateSymbol> predicateSymbols) {
		if (!predicateSymbols.containsKey(func.getName())) {
			predicateSymbols.put(func.getName(),
					new HornClausePredicateSymbol(func.getName(), func.getParameterCount()));
		}
		return predicateSymbols.get(func.getName());
	}

	public Map<HornClausePredicateSymbol, ArrayList<TermVariable>> getBodyPredicateToVars(
			Map<String, HornClausePredicateSymbol> predicateSymbols) {

		final HashMap<HornClausePredicateSymbol, ArrayList<TermVariable>> res = new HashMap<>();
		if (head != null) {
			final ArrayList<TermVariable> vars = new ArrayList<TermVariable>();
			for (final Term par : head.getParameters()) {
				vars.add((TermVariable) par);
			}

			res.put(getHornPredicateSymbol(head.getFunction(), predicateSymbols), vars);
		}
		return res;
	}

	public Map<HornClausePredicateSymbol, ArrayList<TermVariable>> getCobodyPredicateToVars(
			Map<String, HornClausePredicateSymbol> predicateSymbols) {
		return cobody.getPredicateToVars(predicateSymbols);
	}

	public Term getTransitionFormula(Theory theory) {
		return cobody.getTransitionFormula(theory);
	}
}
