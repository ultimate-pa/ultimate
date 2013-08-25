package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.Arrays;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.LetTerm;
import de.uni_freiburg.informatik.ultimate.logic.QuantifiedFormula;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashMap;
import de.uni_freiburg.informatik.ultimate.util.ScopedHashSet;

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
	private final ScopedHashSet<Term> m_VarsInSubstitutionMapping;
	
	public SafeSubstitution(Script script,
			Map<Term, Term> substitutionMapping) {
		super();
		m_Script = script;
		m_ScopedSubstitutionMapping = new ScopedHashMap<Term, Term>();
		m_ScopedSubstitutionMapping.putAll(substitutionMapping);
		m_VarsInSubstitutionMapping = new ScopedHashSet<Term>();
		for (Entry<Term, Term> entry  : m_ScopedSubstitutionMapping.entrySet()) {
			m_VarsInSubstitutionMapping.addAll(Arrays.asList(entry.getKey().getFreeVars()));
			m_VarsInSubstitutionMapping.addAll(Arrays.asList(entry.getValue().getFreeVars()));
		}
	}

	@Override
	protected void convert(Term term) {
		if (m_ScopedSubstitutionMapping.containsKey(term)) {
			setResult(m_ScopedSubstitutionMapping.get(term));
		} else {
			if (term instanceof QuantifiedFormula) {
				m_ScopedSubstitutionMapping.beginScope();
				m_VarsInSubstitutionMapping.beginScope();
				QuantifiedFormula qFormula = (QuantifiedFormula) term;
				for (TermVariable var : qFormula.getVariables()) {
					if (m_VarsInSubstitutionMapping.contains(var)) {
						TermVariable freshVariable = var.getTheory().
								createFreshTermVariable("subst", var.getSort());
						//FIXME uncomment following code once this problem occurs
						throw new UnsupportedOperationException(
								"interference between quantified vars and substitution");
//						m_ScopedSubstitutionMapping.put(var, freshVariable);
//						m_VarsInSubstitutionMapping.add(var);
//						m_VarsInSubstitutionMapping.add(freshVariable);
					}
				}
				
			} else if (term instanceof LetTerm) {
				throw new UnsupportedOperationException("LetTerm not supported");
			}
			super.convert(term);
		}
	}
	

	@Override
	public void postConvertQuantifier(QuantifiedFormula old, Term newBody) {
		Term result;
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
				newQuantifiedVars = old.getVariables();
			}
			result = m_Script.quantifier(old.getQuantifier(), newQuantifiedVars, newBody);
		}
		m_ScopedSubstitutionMapping.endScope();
		m_ScopedSubstitutionMapping.beginScope();
		setResult(result);
	}



}
