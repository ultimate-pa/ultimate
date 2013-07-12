package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.preprocessors;

import java.util.*;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.logic.Util;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.AuxVarGenerator;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker.Preferences.UseDivision;


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
	private static final String s_auxPrefix = "div_aux";
	
	private Script m_script;
	private AuxVarGenerator m_auxVarGenerator;
	private Collection<Term> m_auxTerms;
	
	@Override
	public String getDescription() {
		return "Replace integer division by equivalent linear constraints";
	}
	@Override
	public Term process(Script script, Term term) {
		m_script = script;
		m_auxVarGenerator = new AuxVarGenerator(script, term);
		m_auxTerms = new ArrayList<Term>();
		Term term_new = transform(term);
		return Util.and(script, term_new,
				Util.and(script, m_auxTerms.toArray(new Term[0])));
	}
	
	/**
	 * @return the auxiliary variables generated during the process
	 */
	public Collection<TermVariable> getAuxVars() {
		return m_auxVarGenerator.getAuxVars();
	}
	
	@Override
	protected void convert(Term term) {
		assert(m_script != null);
		if (!(term instanceof ApplicationTerm)) {
			super.convert(term);
			return;
		}
		ApplicationTerm appt = (ApplicationTerm) term;
		String func = appt.getFunction().getName();
		if (func != "div") {
			super.convert(term);
			return;
		}
		assert(appt.getParameters().length == 2);
		Term divident = transform(appt.getParameters()[0]);
		Term divisor  = transform(appt.getParameters()[1]);
		TermVariable auxVar = m_auxVarGenerator.newAuxVar(s_auxPrefix,
				m_script.sort("Int"));
		
		if (Preferences.use_division == UseDivision.C_STYLE) {
			// x < 0 \/ (y*z ≤ x /\ x < (y + 1)*z)
			Term conj1 = m_script.term("and",
				m_script.term("<=", m_script.term("*", divident, divisor),
						auxVar),
				m_script.term("<", auxVar, m_script.term("*", divident,
						m_script.term("+", divisor,
								m_script.numeral(BigInteger.ONE))))
			);
			m_auxTerms.add(m_script.term("or", m_script.term("<", divident,
					m_script.numeral(BigInteger.ZERO)), conj1));
			
			// x ≥ 0 \/ ((y + 1)*z < x /\ x ≤ y*z)
			Term conj2 = m_script.term("and",
					m_script.term("<", m_script.term("*", divident,
							m_script.term("+", divisor,
									m_script.numeral(BigInteger.ONE))), auxVar),
					m_script.term("<=", auxVar,  m_script.term("*", divident,
							divisor))
			);
			m_auxTerms.add(m_script.term("or",
					m_script.term(">=", divident,
							m_script.numeral(BigInteger.ZERO)), conj2)
			);
		} else if (Preferences.use_division == UseDivision.SAFE) {
			m_auxTerms.add(m_script.term("=", m_script.term("*", auxVar, divisor),
					divident));
		} else if (Preferences.use_division == UseDivision.RATIONALS_ONLY) {
			assert(!divident.getSort().equals(m_script.sort("Int")));
		} else {
			assert(false);
		}
		setResult(auxVar);
		return;
	}
}