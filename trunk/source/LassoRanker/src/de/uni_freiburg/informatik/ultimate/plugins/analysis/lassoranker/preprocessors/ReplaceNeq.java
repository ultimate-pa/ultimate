package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;


/**
 * Replaces disequalities—atoms of the form a ≠ b with (a < b \/ a > b).
 * 
 * @author Jan Leike
 */
public class ReplaceNeq extends TermTransformer implements PreProcessor {
	
	private Script m_script = null;

	@Override
	public String getName() {
		return "Replace disequalities";
	}

	@Override
	public String getDescription() {
		return "Replaces atoms of the form a != b with (a < b \\/ a > b).";
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
			String func = appt.getFunction().getName();
			if (func.equals("not")) {
				assert(appt.getParameters().length == 1);
				Term t2 = appt.getParameters()[0];
				if (t2 instanceof ApplicationTerm) {
					ApplicationTerm appt2 = (ApplicationTerm) t2;
					String func2 = appt2.getFunction().getName();
					if (func2 == "=") {
						assert(appt2.getParameters().length == 2);
						Term param1 = m_script.term("<", appt2.getParameters());
						Term param2 = m_script.term(">", appt2.getParameters());
						setResult(m_script.term("or", param1, param2));
						return;
					}
				}
			}
		}
		super.convert(term);
	}
}