package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Replaces equalities (atoms of the form a = b) with (a ≤ b \/ a ≥ b).
 * 
 * @author Jan Leike
 */
public class RewriteEquality extends TermTransformer implements PreProcessor {
	
	private Script m_script;
	
	@Override
	public String getDescription() {
		return "Replaces atoms of the form a = b with (a <= b \\/ a >= b).";
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
			if (appt.getFunction().getName().equals("=") &&
					!appt.getParameters()[0].getSort().getName().equals("Bool")) {
				assert(appt.getParameters().length == 2);
				Term param1 = m_script.term("<=", appt.getParameters());
				Term param2 = m_script.term(">=", appt.getParameters());
				setResult(m_script.term("and", param1, param2));
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