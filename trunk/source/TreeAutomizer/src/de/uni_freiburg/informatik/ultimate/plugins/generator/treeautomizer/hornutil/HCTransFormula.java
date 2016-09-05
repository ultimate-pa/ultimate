package de.uni_freiburg.informatik.ultimate.plugins.generator.treeautomizer.hornutil;

import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class HCTransFormula {
	
	// f: in -> out { f(x1, ..., xn) = formula[] ; } 
	private final Term formula;
	private final Map<HCVar, TermVariable> inVars;
	private final Map<HCVar, TermVariable> outVars;
	
	public Map<HCVar, TermVariable> getInVars() {
		return inVars;
	}

	public Map<HCVar, TermVariable> getOutVars() {
		return outVars;
	}

	
	public HCTransFormula(Term form, Map<HCVar, TermVariable> inV, Map<HCVar, TermVariable> outV) {
		formula = form;
		
		inVars = inV;
		outVars = outV;
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
		return formula.toString();
	}
}
