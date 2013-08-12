package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Substitutes TermVariables by Terms. Takes care that no quantified 
 * TermVariable is substituted. 
 * 
 * @author Matthias Heizmann
 *
 */
public class Substitution {
	private final Map<TermVariable,Term> m_Mapping;
	private final Script m_Script;

	public Substitution(Map<TermVariable, Term> mapping, Script script) {
		m_Mapping = mapping;
		m_Script = script;
	}
	
	public Term transform(Term term) {
		TermVariable[] vars = new TermVariable[m_Mapping.size()];
		Term[] values = new Term[m_Mapping.size()];
		int i=0;
		for (Entry<TermVariable, Term> entry : m_Mapping.entrySet()) {
			vars[i] = entry.getKey();
			values[i] = entry.getValue(); 
			i++;
		}
		Term result = m_Script.let(vars, values, term);
		result = new FormulaUnLet().unlet(result);
		return result;
	}

}
