package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;


/**
 * Remove negation before atoms.
 * 
 * <ul>
 * <li> NOT (a >= b) becomes a < b
 * <li> NOT (a > b) becomes a <= b
 * </ul>
 * 
 * @author Jan Leike
 */
public class RemoveNegation extends TermTransformer implements PreProcessor {
private Script m_script;
	
	@Override
	public String getDescription() {
		return "Removes negation before atoms.";
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
			if (appt.getFunction().getName().equals("not")) {
				assert(appt.getParameters().length == 1);
				Term param = appt.getParameters()[0];
				assert(param instanceof ApplicationTerm);
//				if (!(param instanceof ApplicationTerm)) {
//					throw new TermException("Expected inequality: " + appt);
//				}
				ApplicationTerm appt2 = (ApplicationTerm)param;
				if (appt2.getFunction().getName() == "<=") {
					setResult(m_script.term(">", appt2.getParameters()));
				} else if (appt2.getFunction().getName() == "<") {
					setResult(m_script.term(">=", appt2.getParameters()));
				} else if (appt2.getFunction().getName() == ">=") {
					setResult(m_script.term("<", appt2.getParameters()));
				} else if (appt2.getFunction().getName() == ">") {
					setResult(m_script.term("<=", appt2.getParameters()));
				} else {
					assert(false);
//					throw new TermException("Expected inequality: " + appt);
				}
				return;
			}
		}
		super.convert(term);
	}
	
//	@Override
//	public Collection<TermVariable> getAuxVars() {
//		return Collections.emptyList();
//	}
}
