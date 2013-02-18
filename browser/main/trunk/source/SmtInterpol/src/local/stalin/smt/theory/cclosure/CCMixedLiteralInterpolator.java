package local.stalin.smt.theory.cclosure;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import local.stalin.logic.Formula;
import local.stalin.logic.FormulaVariable;
import local.stalin.logic.Term;
import local.stalin.logic.TermVariable;
import local.stalin.logic.Theory;
import local.stalin.smt.dpll.DPLLAtom;
import local.stalin.smt.dpll.DPLLEngine;
import local.stalin.smt.dpll.InterpolationInfo;
import local.stalin.smt.dpll.Interpolator;

/**
 * Interpolator for mixed literals  <code>a = b</code>, where a is a A-local term and b a B-local term.
 * Every mixed literal has a unique term variable "mix" which is considered to be shared.  It may appear in
 * interpolants for the clauses "a!=b \/ ...", which have no corresponding interpolators.  The clauses
 * of the form "a=b \/..." have an instance of this class as interpolator.  The interpolant of the clause 
 * contains one or more formula variable: I[F1][F2]...  Each formula variable is associated with some 
 * shared term s1,s2,..., which is represented by the member <code>replacements</code>.  The interpolant 
 * for the clause "a=b \/ C" satisfy the equations
 * <pre>
 *   A ==> I[a=s1][a=s2]... \/ C \ B
 *   B /\ I[b!=s1][b!=s2]... ==> C \downarrow B
 * </pre>
 * 
 * On interpolation on the literal a!=b, the other interpolant is substituted for the formula variables Fi,
 * where the shared term variable "mix" in the other interpolant is replaced by the shared term si.
 * <pre>
 *   I[otherI[s1\mix]][otherI[s2\mix]]...
 * </pre>
 * @author hoenicke
 */
public class CCMixedLiteralInterpolator implements Interpolator {
	Theory theory;
	TermVariable termVar;
	private Map<FormulaVariable, Term> replacements;
	
	public CCMixedLiteralInterpolator(Theory t, TermVariable tvar, FormulaVariable fvar, Term sharedTerms) {
		theory = t;
		termVar = tvar;
		replacements = Collections.singletonMap(fvar, sharedTerms);
	}
	
	public CCMixedLiteralInterpolator(Theory t, TermVariable tvar, Map<FormulaVariable, Term> repl) {
		theory = t;
		termVar = tvar;
		replacements = repl;
	}
	
	public Interpolator merge(Interpolator other) {
		if (other instanceof CCMixedLiteralInterpolator) {
			CCMixedLiteralInterpolator otherMixed = (CCMixedLiteralInterpolator) other;  			
			assert (termVar == otherMixed.termVar);
			HashMap<FormulaVariable, Term> newMap = new HashMap<FormulaVariable, Term>();
			newMap.putAll(replacements);
			newMap.putAll(otherMixed.replacements);
			return new CCMixedLiteralInterpolator(theory, termVar, newMap);
		} else {
			throw new UnsupportedOperationException("Implement merge for a <= b and a = b");
		}
	}
	
	@Override
	public InterpolationInfo interpolate(DPLLEngine engine, DPLLAtom atom,
			int fnr, InterpolationInfo interpolationInfo,
			InterpolationInfo otherInfo) {
		Theory t = engine.getSMTTheory();
		Formula result = interpolationInfo.getFormula();
		HashMap<DPLLAtom,Interpolator> interpolators = 
			new HashMap<DPLLAtom, Interpolator>(interpolationInfo.getInterpolators());
		interpolators.remove(atom);
		for (Entry<DPLLAtom, Interpolator> interpolEntry : otherInfo.getInterpolators().entrySet()) {
			DPLLAtom key = interpolEntry.getKey();
			if (key == atom)
				continue;
			Interpolator otherInterpolator = interpolEntry.getValue();
			if (interpolators.containsKey(key)) {
				interpolators.put(key, interpolators.get(key).merge(otherInterpolator));
			} else {
				interpolators.put(key, otherInterpolator);
			}
		}
		for (Entry<FormulaVariable, Term> entry : replacements.entrySet()) {
			Formula subst = otherInfo.getFormula();
			if (entry.getValue() != t.term(termVar)) 
				subst = t.let(termVar, entry.getValue(), subst);
			result = t.flet(entry.getKey(), subst, result); 
		}
		return new InterpolationInfo(result, interpolators);
	}
	
	public String toString() {
		return "Substitutions: " + replacements;
	}
	
}
