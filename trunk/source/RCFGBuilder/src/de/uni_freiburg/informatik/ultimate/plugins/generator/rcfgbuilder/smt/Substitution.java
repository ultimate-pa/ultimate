package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.logic.FormulaUnLet;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;


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
	
	private final static boolean USE_SAFE_SUBSTITUTION = true;

	public Substitution(Map<TermVariable, Term> mapping, Script script) {
		m_Mapping = mapping;
		m_Script = script;
	}
	
	public Term transform(Term term) {
		Term result = withLet(term);
		if (USE_SAFE_SUBSTITUTION) {
			Term resultSS = withSS(term);
			assert (Util.checkSat(m_Script, 
					m_Script.term("distinct", result, resultSS)) == LBool.UNSAT) : 
						"Bug in safe substitution.";
			result = resultSS;
		}
		return result;
	}
	
	private Term withLet(Term term) {
		TermVariable[] vars = new TermVariable[m_Mapping.size()];
		Term[] values = new Term[m_Mapping.size()];
		int i=0;
		for (Entry<TermVariable, Term> entry : m_Mapping.entrySet()) {
			vars[i] = entry.getKey();
			assert vars[i] != null : "substitution of null";
			values[i] = entry.getValue(); 
			assert values[i] != null : "substitution by null";
			i++;
		}
		Term result = m_Script.let(vars, values, term);
		result = new FormulaUnLet().unlet(result);
		return result;
	}
	
	private Term withSS(Term term) {
		Map<Term, Term> mapping = new HashMap<Term, Term>();
		for (Entry<TermVariable, Term> entry : m_Mapping.entrySet()) {
			mapping.put(entry.getKey(), entry.getValue());
		}
		Term result = (new SafeSubstitution(m_Script, mapping)).transform(term);
		return result;
	}

}
