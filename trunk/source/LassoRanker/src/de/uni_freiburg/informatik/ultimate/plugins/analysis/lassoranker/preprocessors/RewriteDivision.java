package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;


/**
 * Replace integer division by equivalent linear constraints:
 * Every occurrence of "div x y" is replaced with
 * <pre>
 * (x < 0 \/ (y*z <= x /\ x < (y + 1)*z)) /\
 * (x >= 0 \/ ((y + 1)*z < x /\ x <= y*z))
 * </pre>
 * Introduces new auxiliary variables and auxiliary terms.
 * 
 * Does not check if all statements are linear.
 * 
 * @author Jan Leike
 */
public class RewriteDivision extends TermTransformer implements PreProcessor {
	
	private Script m_script;
	private Collection<TermVariable> m_auxVars;
	private Collection<Term> m_auxTerms;
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		m_auxVars = new ArrayList<TermVariable>();
		Term term_new = transform(term);
		return Util.and(script, term_new,
				Util.and(script, m_auxTerms.toArray(new Term[0])));
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
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appt = (ApplicationTerm) term;
			String func = appt.getFunction().getName();
			if (func == "div") {
				assert(appt.getParameters().length == 2);
				Term divident = transform(appt.getParameters()[0]);
				Term divisor  = transform(appt.getParameters()[1]);
				String name = s_auxPrefix + m_auxNameIndex;
				m_auxNameIndex++;
				Term auxVar = m_script.variable(name, m_script.sort("Int"));
				m_auxVars.add((TermVariable) auxVar);
				
				// x < 0 \/ (y*z ≤ x /\ x < (y + 1)*z)
				Term conj1 = m_script.term("and",
					m_script.term("<=", m_script.term("*",
							divident, divisor), auxVar),
					m_script.term("<", auxVar, m_script.term("*",
							divident, m_script.term("+", divisor,
									m_script.numeral(BigInteger.ONE)))));
				m_auxTerms.add(m_script.term("or",
						m_script.term("<", divident,
								m_script.numeral(BigInteger.ZERO)), conj1));
				
				// x ≥ 0 \/ ((y + 1)*z < x /\ x ≤ y*z)
				Term conj2 = m_script.term("and",
						m_script.term("<", m_script.term("*",
								divident, m_script.term("+", divisor,
								m_script.numeral(BigInteger.ONE))), auxVar),
						m_script.term("<=", auxVar,  m_script.term("*",
										divident, divisor)));
				m_auxTerms.add(m_script.term("or",
						m_script.term(">=", divident,
								m_script.numeral(BigInteger.ZERO)), conj2));
				setResult(auxVar);
				return;
			}
		}
		super.convert(term);
	}
}
