package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxVarManager;


/**
 * Replaces booleans variables b by integer auxiliary variables aux_b whose
 * meaning is aux_b = (ite b 1 0) 
 * 
 * @author Jan Leike, Matthias Heizmann
 */
public class RewriteBooleans extends TermTransformer implements PreProcessor {
	private static final String s_auxInfix = "_bool";
	
	private Script m_Script;
	private final AuxVarManager m_AuxVarManager;
	
	public RewriteBooleans(AuxVarManager auxVarManager) {
		m_AuxVarManager = auxVarManager;
	}
	
	@Override
	public String getDescription() {
		return "Replaces boolean variables b by auxiliary integer variables";
	}

	
	@Override
	public Term process(Script script, Term term) {
		m_Script = script;
		return (new RewriteBooleanHelper()).transform(term);
	}

	
	/**
	 * Given the Term booleanTerm whose Sort is "Bool" return the term
	 * (ite booleanTerm one zero)
	 */
	private Term getDefinition(Term booleanTerm) {
		assert booleanTerm.getSort().getName().equals("Bool");
		Term one = m_Script.numeral(BigInteger.ONE);
		Term zero = m_Script.numeral(BigInteger.ZERO);
		return m_Script.term("ite", booleanTerm, one, zero);
	}
	
	/**
	 * TermTransformer that replaces Boolean TermVariables.  
	 *
	 */
	private class RewriteBooleanHelper extends TermTransformer {
		@Override
		protected void convert(Term term) {
			assert(m_Script != null);
			if (term instanceof TermVariable &&
					term.getSort().getName().equals("Bool")) {
				Term definition = getDefinition(term);
				Term one = m_Script.numeral(BigInteger.ONE);
				TermVariable auxVar = 
						m_AuxVarManager.constructAuxVar(s_auxInfix, definition);
				Term auxTerm = m_Script.term(">=", auxVar, one);
				setResult(auxTerm);
				return;
			}
			super.convert(term);
		}
	}
}