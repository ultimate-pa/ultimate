package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;

/**
 * Substitution that replaces subterms by terms. Takes care the quantified
 * variables are renamed to fresh variables such that 
 * - no variable in substituted term is "captured" by an existing quantifier
 * - no subterm that contains a bound variable is substituted.
 * 
 * Idea of this implementation. Replace quantified variables by fresh variables
 * whenever a variable interferes with a variable in the substitution mapping.
 * TODO: If quantified variable occurs in key of substitution mapping, do not
 * rename quantified variable but remove substitution in the current scope.
 * @author Matthias Heizmann
 */
public class SafeSubstitution extends TermTransformer {
	
	private final Script m_Script;
	private final ScopedHashMap<Term,Term> m_ScopedSubstitutionMapping;
	
	public SafeSubstitution(Script script,
			Map<Term, Term> substitutionMapping) {
		super();
		m_Script = script;
		m_ScopedSubstitutionMapping = new ScopedHashMap<Term, Term>();
		m_ScopedSubstitutionMapping.putAll(substitutionMapping);
	}

	@Override
	protected void convert(Term term) {
		if (m_ScopedSubstitutionMapping.containsKey(term)) {
			setResult(m_ScopedSubstitutionMapping.get(term));
		} else {
			if (term instanceof QuantifiedFormula) {
				m_ScopedSubstitutionMapping.beginScope();
				QuantifiedFormula qFormula = (QuantifiedFormula) term;
				removeQuantifiedVarContainingKeys(qFormula);
				renameQuantifiedVarsThatOccurInValues(qFormula);
			} else if (term instanceof LetTerm) {
				throw new UnsupportedOperationException("LetTerm not supported");
			}
			super.convert(term);
		}
	}

	/**
	 * Rename all quantified variables (in the current scope) that occur in 
	 * values of the substitution mapping (of the current scope).
	 * We use fresh names that never occurred before.
	 * This avoids that after the substitution a variables in a substituted
	 * subterm is "accidently" captured by a quantifier.
	 */
	private void renameQuantifiedVarsThatOccurInValues(QuantifiedFormula qFormula) {
		Set<TermVariable> toRename = 
				varsOccuringInValues(qFormula.getVariables(), m_ScopedSubstitutionMapping);
		for (TermVariable var : toRename) {
				TermVariable freshVariable = var.getTheory().
						createFreshTermVariable("subst", var.getSort());
				m_ScopedSubstitutionMapping.put(var, freshVariable);
		}
	}


	/**
	 * Remove from (current scope of) substitution mapping
	 * all substitutions where the key contains a variables that is
	 * quantified in this scope.
	 * 
	 */
	private void removeQuantifiedVarContainingKeys(QuantifiedFormula qFormula) {

		Iterator<Entry<Term, Term>> it = 
				m_ScopedSubstitutionMapping.entrySet().iterator();
		while (it.hasNext()) {
			Entry<Term, Term> entry = it.next();
			List<TermVariable> quantifiedVars = Arrays.asList(qFormula.getVariables());
			List<TermVariable> occuringVars = Arrays.asList(entry.getKey().getFreeVars());
			if (!Collections.disjoint(quantifiedVars, occuringVars)) {
				it.remove();
			}
		}
	}
	
	/**
	 * Returns the subset of vars that occur as free variables in the values of
	 * map.
	 */
	private static Set<TermVariable> varsOccuringInValues(TermVariable vars[], Map<?,Term> map) {
		Set<TermVariable> result = null;
		for (Term term  : map.values()) {
			for (TermVariable tv : term.getFreeVars()) {
				if (Arrays.asList(vars).contains(tv)) {
					result = addToSet(tv,result);
				}
			}
		}
		if (result == null) {
			result = Collections.emptySet();
		}
		return result;
	}


	/**
	 * Add tv to set and return set. Construct HashSet if set is null.
	 */
	private static Set<TermVariable> addToSet(TermVariable tv, Set<TermVariable> set) {
		if (set == null) {
			set = new HashSet<TermVariable>();
		}
		set.add(tv);
		return set;
	}

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		Term result;
		// to avoid capturing of variables we had to rename quantified vars
		// to fresh vars in subterms. Now we have to construct the appropriate
		// supterterm.
		// How can we detect if a variable was renamed?
		// If a variable (of the old superterm) was renamed, it is a key in the
		// current substitution mapping.
		TermVariable[] newQuantifiedVars = 
									new TermVariable[old.getVariables().length];
		boolean quantifiedVariablesChanged = false;
		for (int i=0; i<old.getVariables().length; i++) {
			if (m_ScopedSubstitutionMapping.containsKey(old.getVariables()[i])) {
				newQuantifiedVars[i] = old.getVariables()[i];
				quantifiedVariablesChanged = true;
			} else {
				newQuantifiedVars[i] = old.getVariables()[i];
			}
		}
		if (old.getSubformula() == newBody) {
			assert !quantifiedVariablesChanged;
			result = old;
		} else {
			if (!quantifiedVariablesChanged) {
				// reuse old array
				newQuantifiedVars = old.getVariables();
			}
			result = m_Script.quantifier(old.getQuantifier(), newQuantifiedVars, newBody);
		}
		m_ScopedSubstitutionMapping.endScope();
		setResult(result);
	}

	@Override
	public String toString() {
		return "Substitution " + m_ScopedSubstitutionMapping.toString();
	}



}
