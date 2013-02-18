package de.uni_freiburg.informatik.ultimate.modelcheckerutils.staticutils;

import de.uni_freiburg.informatik.ultimate.logic.Annotation;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBException;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.Script.LBool;

public class SMTInterface {
	
	static Script m_Script = null;
	
	public SMTInterface(Script script) {
		m_Script = script;
	}
	
	public LBool checkSatisfiable(Term f) {
	    LBool result = null;
	    m_Script.push(1);
	    try {
	    	m_Script.assertTerm(f);
	    } catch (SMTLIBException e) {
			m_Script.pop(1);
			throw e;
	    }
	    result = m_Script.checkSat();
	    m_Script.pop(1);
		return result;
	}


	public Term[] computeInterpolants(Term[] interpolInput) {
		Term[] annotatedTerms = new Term[interpolInput.length];
		Term[] constantsRepresentingAnnotatedTerms = new Term[interpolInput.length];
		m_Script.push(1);
		for (int i = 0; i < interpolInput.length; i++) {
			String name = "term-" + i;
			
			annotatedTerms[i] = m_Script.annotate(interpolInput[i], new Annotation(":named", name));
			m_Script.assertTerm(annotatedTerms[i]);
			constantsRepresentingAnnotatedTerms[i] = m_Script.term(name);
		}
		Term[] result;
		LBool isSat = m_Script.checkSat();
		if (isSat == LBool.SAT) {
			result = null;
		} else if (isSat == LBool.UNSAT) {
			result = m_Script.getInterpolants(constantsRepresentingAnnotatedTerms);
			m_Script.pop(1);
		} else if (isSat == LBool.UNKNOWN){
			throw new SMTLIBException("Result: UNKNOWN.");
		} else {
			throw new IllegalArgumentException();
		}
//		m_Script.pop(1);
		return result;
	}
}