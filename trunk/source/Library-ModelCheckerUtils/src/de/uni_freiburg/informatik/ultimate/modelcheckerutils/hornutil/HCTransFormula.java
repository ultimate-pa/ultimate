package de.uni_freiburg.informatik.ultimate.modelcheckerutils.hornutil;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.transitions.TransFormula;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVar;



public class HCTransFormula extends TransFormula {
	
	// f: in -> out { f(x1, ..., xn) = formula[] ; } 
	private final Term formula;
	
	public int getArity() {
		return Math.max(1, mInVars.size());
	}
	public Map<IProgramVar, TermVariable> getInVars() {
		return mInVars;
	}

	public Map<IProgramVar, TermVariable> getOutVars() {
		return mOutVars;
	}
	
	public HCTransFormula(final Term form, final Map<IProgramVar, TermVariable> inV, final Map<IProgramVar, TermVariable> outV) {
		super(inV, outV, new HashSet<>(), new HashSet<>());
		formula = form;
	}
	
	
	private Set<TermVariable> getVars(Term t) {
		final Set<TermVariable> res = new HashSet<TermVariable>();
		
		if (t instanceof TermVariable) {
			res.add((TermVariable) t);
		}
		
		if (t instanceof ApplicationTerm) {
			for (final Term s : ((ApplicationTerm) t).getParameters()) {
				res.addAll(getVars(s));
			}
		}
		return res;
	}
	
	public Term getFormula() {
		return formula;
	}
	
	@Override
	public String toString() {
		return formula.toString() + ",in: " + mInVars + ",out: " + mOutVars;
	}
	/*
	@Override
	public int hashCode() {
		return formula.hashCode();
	}
	*/
	@Override
	public Set<IProgramVar> getAssignedVars() {
		// TODO Auto-generated method stub
		return null;
	}
}
