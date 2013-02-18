package local.stalin.smt.theory.cclosure;

import local.stalin.logic.FunctionSymbol;
import local.stalin.logic.PredicateSymbol;

public class CCBaseTerm extends CCTerm {
	Object symbol;
	int firstFormula, lastFormula;
	
	public CCBaseTerm(boolean isFunc, int numParents, Object symb) {
		super(isFunc, numParents);
		this.symbol = symb;
		firstFormula = Integer.MAX_VALUE; lastFormula = -1;
	}

	/**
	 * Create a CCBaseTerm that is not part of the e-graph and is only used for interpolation.
	 * @param symb
	 */
	public CCBaseTerm(Object symb) {
		super();
		this.symbol = symb;
	}
	
	public int getFirstFormula() {
		return firstFormula;
	}
	
	public int getLastFormula() {
		return lastFormula;
	}

	public void occursIn(int formulaNr) {
		if (formulaNr < firstFormula)
			firstFormula = formulaNr;
		if (formulaNr > lastFormula)
			lastFormula = formulaNr;
	}
	
	public String toString() {
		if (symbol instanceof FunctionSymbol)
			return ((FunctionSymbol)symbol).getName();
		if (symbol instanceof PredicateSymbol)
			return ((PredicateSymbol)symbol).getName();
		return symbol.toString();
	}
}
