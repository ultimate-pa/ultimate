package de.uni_freiburg.informatik.ultimate.modelcheckerutils.transfomers;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

public class SSATermTransformer extends TermTransformer{

	private HashMap<TermVariable, TermVariable> m_VariableMapping 	= null;
	
	
	public SSATermTransformer(Script script, HashMap<TermVariable, TermVariable> variableMapping){
		m_VariableMapping	= variableMapping;
	}
	
	protected void convert(Term term) {
		if (term instanceof TermVariable) {
			TermVariable tv		= (TermVariable) term;
			if (m_VariableMapping.containsKey(tv)){
				super.setResult(m_VariableMapping.get(tv));
				return;
			}
		}
		super.convert(term);
	}
}
