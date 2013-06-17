package de.uni_freiburg.informatik.ultimate.plugins.ic3modelchecker;

import java.util.HashMap;
import java.util.HashSet;

import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class ConstSubstResult {
	private HashMap<Term, Term> substMap;
	private Term substTerm;
	
	public ConstSubstResult(HashMap<Term, Term> substMap, Term substTerm) {
		this.substMap = substMap;
		this.substTerm = substTerm;
	}
	
	public HashMap<Term, Term> getMap() {
		return substMap;
	}
	
	public Term getSubstTerm() {
		return substTerm;
	}
	
	public HashSet<TermVariable> getSubstitutedTermVars() {
		HashSet<TermVariable> result = new HashSet<TermVariable>();
		for (Term key : substMap.keySet()) {
			result.add((TermVariable) key);
		}
		return result;
	}
}
