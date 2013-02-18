package local.stalin.smt.theory.cclosure;

import local.stalin.logic.EqualsAtom;
import local.stalin.logic.Formula;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.logic.VariableTerm;
import local.stalin.smt.dpll.DPLLAtom;


public class EqualityAtom extends DPLLAtom {
	private static int counter = 0;
	private CCTerm c1, c2;
	int ctr = counter++;
	private int firstNr, lastNr;
	private CClosure cclosure;
	private CCTerm mixedTerm;
	
	EqualityAtom(CClosure cclosure, CCTerm c1, CCTerm c2) {
		this(cclosure, c1, c2, null);
	}
	
	EqualityAtom(CClosure cclosure, CCTerm c1, CCTerm c2, TermVariable mixedVar) {
		this.cclosure = cclosure;
		this.c1 = c1;
		this.c2 = c2;
		if (c1.getFirstFormula() > c2.getLastFormula()) {
			/* swap c1 and c2, so that c2 is always the b-local term */
			this.c2 = c1;
			this.c1 = c2;
		}
		if (mixedVar == null) {
			firstNr = lastNr = -1;
		} else {
			firstNr = Math.max(c1.getFirstFormula(), c2.getFirstFormula());
			lastNr = Math.min(c1.getLastFormula(), c2.getLastFormula());
			assert (firstNr > lastNr);
			Theory t = cclosure.engine.getSMTTheory();
			mixedTerm = new CCBaseTerm(t.term(mixedVar));
		}
	}
	
	public CCTerm getLhs() {
		return c1;
	}

	public CCTerm getRhs() {
		return c2;
	}
	
	public boolean isMixed() {
		return firstNr > lastNr;
	}

	@Override
	public int getFirstFormulaNr() {
		if (firstNr == -1) {
			firstNr = Math.max(c1.getFirstFormula(), c2.getFirstFormula());
			lastNr = Math.min(c1.getLastFormula(), c2.getLastFormula());
		}
		return firstNr;
	}

	@Override
	public int getLastFormulaNr() {
		if (firstNr == -1) {
			firstNr = Math.max(c1.getFirstFormula(), c2.getFirstFormula());
			lastNr = Math.min(c1.getLastFormula(), c2.getLastFormula());
		}
		return lastNr;
	}
	
	public CCTerm getMixedInterpolationTerm() {
		assert mixedTerm != null;
		return mixedTerm;
	}

	public TermVariable getMixedInterpolationTermVar() {
		CCTerm term = getMixedInterpolationTerm();
		return ((VariableTerm) cclosure.convertTermToSMT(term)).getVariable();
	}

	public String toString() {
		return "["+ctr+"]"+c1.toString() + " == " + c2.toString();
	}
	
	public String toStringNegated() {
		return "["+ctr+"]"+c1.toString() + " != " + c2.toString();
	}
	
	public Formula getSMTFormula(local.stalin.logic.Theory smtTheory) {
		return cclosure.convertEqualityToSMT(c1, c2);
	}

	@Override
	public int containsTerm(Term t) {
		Formula me = getSMTFormula(/*FIXME*/null);
		Term[] params = me instanceof EqualsAtom ? ((EqualsAtom)me).getTerms() : ((PredicateAtom)me).getParameters();
		for( Term p : params )
			if( p.containsSubTerm(t) )
				return 1;
		return 0;
	}
}
