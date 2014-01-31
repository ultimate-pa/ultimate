package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;


/**
 * Replace strict inequalities that compare terms of sort int by equivalent
 * non-strict inequalities. E.g., the term <i>x > 0</i> is replaced by the term
 * <i> x >= 1</i>. 
 * @author Matthias Heizmann
 */
public class RewriteStrictInequalities implements PreProcessor {
	private Script m_Script;

	/**
	 * Use assert statement to check if result is equivalent to the input.
	 */
	private static final boolean s_CheckResult = true;
	
	@Override
	public String getDescription() {
		return "Replace strict inequalities by non-strict inequalities";
	}
	
	@Override
	public Term process(Script script, Term term) {
		assert m_Script == null;
		m_Script = script;
		Term result = (new RewriteStrictInequalitiesHelper()).transform(term);
		assert !s_CheckResult || !isIncorrect(term, result);
		return result;
	}
	
	/**
	 * Return true if we were able to prove that the result is incorrect.
	 */
	private boolean isIncorrect(Term input, Term result) {
		return (Util.checkSat(m_Script, m_Script.term("distinct", 
				input, result)) == LBool.SAT);
	}

	/**
	 * Replace strict inequalities that compare terms of sort Int by equivalent
	 * non-strict inequalities.
	 *
	 */
	private class RewriteStrictInequalitiesHelper extends TermTransformer {
		
		@Override
		protected void convert(Term term) {
			if (term instanceof ApplicationTerm) {
				ApplicationTerm appTerm = (ApplicationTerm) term;
				String functionSymbolName = appTerm.getFunction().getName();
				Term result = null;
				if (functionSymbolName.equals("<")) {
					result = computeCorrespondingInequality(appTerm);
				} else if (functionSymbolName.equals(">")) {
					result = computeCorrespondingInequality(appTerm);
				}
				if (result != null) {
					setResult(result);
					return;
				}
			}
			super.convert(term);
		}
		
		/**
		 * Requires that appTerm has function symbol "<" or ">" and that
		 * appTerm has two parameters.
		 * If the parameters are of Sort int, we return the corresponding 
		 * equivalent non-strict inequality.
		 * Otherwise we return null.
		 */
		private Term computeCorrespondingInequality(ApplicationTerm appTerm) {
			String functionSymbolName = appTerm.getFunction().getName();
			if (appTerm.getParameters().length != 2) {
				throw new AssertionError("expected binay terms");
			}
			if (!appTerm.getParameters()[0].getSort().getName().equals("Int")) {
				return null;
			}
			Term one = m_Script.numeral(BigInteger.ONE);
			Term result;
			if (functionSymbolName.equals("<")) {
				result = m_Script.term("<=",
						m_Script.term("+",	appTerm.getParameters()[0], one), 
						appTerm.getParameters()[1]);
			} else if (functionSymbolName.equals(">")) {
				result = m_Script.term(">=", 
						appTerm.getParameters()[0], 
						m_Script.term("+", appTerm.getParameters()[1], one));
			} else {
				throw new AssertionError();
			}
			return result;
		}
	}
}