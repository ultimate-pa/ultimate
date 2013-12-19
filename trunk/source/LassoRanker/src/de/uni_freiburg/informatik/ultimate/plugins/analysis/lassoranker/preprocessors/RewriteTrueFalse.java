package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Rewrite 'true' as '0 >= 0' and 'false' as '0 >= 1'.
 * 
 * @author Jan Leike
 */
public class RewriteTrueFalse extends TermTransformer implements PreProcessor {

	private Script m_script;
	
	@Override
	public String getDescription() {
		return "Replaces 'true' with '0 >= 0' and 'false' with '0 >= 1";
	}

	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		return transform(term);
	}
	
	@Override
	protected void convert(Term term) {
		assert(m_script != null);
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			if (appt.getFunction().getName().equals("true")) {
				assert(appt.getParameters().length == 0);
				setResult(m_script.term(">=", m_script.decimal("0"),
						m_script.decimal("0")));
				return;
			}
			if (appt.getFunction().getName().equals("false")) {
				assert(appt.getParameters().length == 0);
				setResult(m_script.term(">=", m_script.decimal("0"),
						m_script.decimal("1")));
				return;
			}
		}
		super.convert(term);
	}
	
	@Override
	public Collection<TermVariable> getAuxVars() {
		return Collections.emptyList();
	}
}
