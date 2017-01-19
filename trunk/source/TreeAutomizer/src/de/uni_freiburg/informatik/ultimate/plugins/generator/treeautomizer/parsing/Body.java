package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.parsing;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Theory;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HCSymbolTable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClause;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil.HornClausePredicateSymbol;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.managedscript.ManagedScript;

public class Body {
	Cobody cobody;
	ApplicationTerm head;
	
	public Body() {
		cobody = new Cobody();
	}

	public void addPredicateToCobody(ApplicationTerm literal) {
		cobody.addPredicate(literal);
	}

	public HornClause convertToHornClause(final ManagedScript script, final HCSymbolTable symbolTable,
			Theory theory) {
		final Map<HornClausePredicateSymbol, List<TermVariable>> tt = getBodyPredicateToVars(symbolTable);
		assert tt.size() <= 1;
		final HornClausePredicateSymbol bodySymbol = tt.keySet().iterator().hasNext() ? tt.keySet().iterator().next()
				: new HornClausePredicateSymbol.HornClauseFalsePredicateSymbol();
		return new HornClause(script, symbolTable, getTransitionFormula(theory),
				tt.containsKey(bodySymbol) ? tt.get(bodySymbol) : new ArrayList<>(), bodySymbol,
				getCobodyPredicateToVars(symbolTable));

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

	// moved this to HCSymbolTable
//	private HornClausePredicateSymbol getHornPredicateSymbol(FunctionSymbol func,
//			Map<String, HornClausePredicateSymbol> predicateSymbols) {
//		if (!predicateSymbols.containsKey(func.getName())) {
//			predicateSymbols.put(func.getName(),
//					new HornClausePredicateSymbol(symbolTable, func.getName(), func.getParameterSorts().length));
//		}
//		return predicateSymbols.get(func.getName());
//	}

	private Map<HornClausePredicateSymbol, List<TermVariable>> getBodyPredicateToVars(
			final HCSymbolTable symbolTable) {

		final HashMap<HornClausePredicateSymbol, List<TermVariable>> res = new HashMap<>();
		if (head != null) {
			final ArrayList<TermVariable> vars = new ArrayList<>();
			for (final Term par : head.getParameters()) {
				vars.add((TermVariable) par);
			}

//			res.put(getHornPredicateSymbol(head.getFunction(), predicateSymbols), vars);
			res.put(symbolTable.getOrConstructHornClausePredicateSymbol(
						head.getFunction()), 
					vars);
		}
		return res;
	}

	public Map<HornClausePredicateSymbol, List<TermVariable>> getCobodyPredicateToVars(
			HCSymbolTable symbolTable) {
		return cobody.getPredicateToVars(symbolTable);
	}

	public Term getTransitionFormula(Theory theory) {
		return cobody.getTransitionFormula(theory);
	}
}
