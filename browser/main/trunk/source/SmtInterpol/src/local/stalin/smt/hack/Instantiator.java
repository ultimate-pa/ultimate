/**
 * 
 */
package local.stalin.smt.hack;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import local.stalin.logic.ApplicationTerm;
import local.stalin.logic.Formula;
import local.stalin.logic.ITETerm;
import local.stalin.logic.PredicateAtom;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.VariableTerm;
import local.stalin.logic.FormulaWalker.SymbolVisitor;

public class Instantiator implements SymbolVisitor {
	private Map<TermVariable,Term> minst;
	private List<TermVariable> mmask;
	public Instantiator(Map<TermVariable,Term> inst) {
		minst = inst;
		mmask = new ArrayList<TermVariable>();
	}
	@Override
	public void done(Term input) {}
	@Override
	public void done(PredicateAtom pa) {}
	@Override
	public void endscope(TermVariable tv) {
		mmask.remove(tv);
	}
	@Override
	public void endscopes(TermVariable[] tvs) {
		for( TermVariable t : tvs )
			mmask.remove(t);
	}
	@Override
	public void let(TermVariable tv, Term mval) {
		mmask.add(tv);
	}
	@Override
	public Formula predicate(PredicateAtom pa) {
		// Trigger parameter descending
		return null;
	}
	@Override
	public void quantifier(TermVariable[] tvs) {
		for( TermVariable t : tvs )
			mmask.add(t);
	}
	@Override
	public Term term(Term input) {
		if( input instanceof ApplicationTerm || input instanceof ITETerm )
			// Trigger argument descending
			return null;
		if( input instanceof VariableTerm ) {
			TermVariable tv = ((VariableTerm)input).getVariable();
			if( mmask.contains(tv) )
				return input;// is masked!!!
			Term result = minst.get(tv);
			return result != null ? result : input;
		}
		return input;
	}
	@Override
	public boolean unflet() {
		return false;
	}
	@Override
	public boolean unlet() {
		return false;
	}
}