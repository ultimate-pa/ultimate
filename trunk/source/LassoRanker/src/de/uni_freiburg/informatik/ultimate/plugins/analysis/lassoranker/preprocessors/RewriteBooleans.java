package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.ArrayList;
import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Replaces booleans variables b with b_bool > 0 where b_bool is a new variable
 * 
 * @author Jan Leike
 */
public class RewriteBooleans extends TermTransformer implements PreProcessor {
	
	private Script m_script;
	private Collection<TermVariable> m_auxVars;
	
	@Override
	public String getDescription() {
		return "Replaces boolean variables with b_bool > 0 "
				+ "where b_bool is a new variable";
	}
	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		m_auxVars = new ArrayList<TermVariable>();
		return transform(term);
	}
	
	/**
	 * @return the auxiliary variables generated during the process
	 */
	public Collection<TermVariable> getAuxVars() {
		return m_auxVars;
	}
	
	@Override
	protected void convert(Term term) {
		assert(m_script != null);
		if (term instanceof TermVariable &&
				term.getSort().getName().equals("Bool")) {
			TermVariable b = m_script.variable(((TermVariable) term).getName()
					+ "_bool", m_script.sort("Real"));
			m_auxVars.add(b);
			setResult(m_script.term(">=", b, m_script.decimal("1")));
			return;
		}
		super.convert(term);
	}
}