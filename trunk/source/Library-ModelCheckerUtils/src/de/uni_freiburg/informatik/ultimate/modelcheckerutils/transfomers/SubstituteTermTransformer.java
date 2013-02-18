package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;

import java.util.HashMap;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;

public class SubstituteTermTransformer extends TermTransformer{

//	private Term m_term = null;
//	private Term m_substitute = null;
	private HashMap<Term, Term> m_substitution = new HashMap<Term, Term>();
	
	public Term substitute(Term formula, Term term, Term substitute) {
//		m_term = term;
//		m_substitute = substitute;
		m_substitution.clear();
		m_substitution.put(term, substitute);
		Term result = transform(formula);
		return result;
	}
	
	public Term substitute(Term formula, HashMap<Term,Term> substitution) {
		m_substitution = substitution;
		Term result = transform(formula);
		return result;
	}
	
	protected void convert(Term term) {
		if (m_substitution.containsKey(term)) {
			super.setResult(m_substitution.get(term));
			return;
		}
		super.convert(term);
	}
	
}
