package local.stalin.smt.dpll;

import local.stalin.logic.Formula;
import local.stalin.logic.Term;

public class NamedAtom extends DPLLAtom {
	final Object name;
	final Formula smtAtom;
	int firstNr, lastNr;
	
	public NamedAtom(Object name, Formula smtAtom) {
		this.name = name;
		this.smtAtom = smtAtom;
		this.firstNr = Integer.MAX_VALUE;
		this.lastNr = 0;
	}
	
	public String toString() {
		return name.toString();
	}
	public void occursIn(int formulaNr) {
		if (firstNr > formulaNr)
			firstNr = formulaNr;
		if (lastNr < formulaNr)
			lastNr = formulaNr;
	}

	@Override
	public int getFirstFormulaNr() {
		return firstNr;
	}
	
	@Override
	public int getLastFormulaNr() {
		return lastNr;
	}

	public Formula getSMTFormula(local.stalin.logic.Theory smtTheory) {
		return smtAtom;
	}
	public int containsTerm(Term t) {
		return 0;
	}
}
