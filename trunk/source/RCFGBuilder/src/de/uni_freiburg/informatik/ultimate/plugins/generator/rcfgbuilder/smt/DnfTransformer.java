package de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.smt;

import de.uni_freiburg.informatik.ultimate.logic.ApplicationTerm;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermTransformer;
import de.uni_freiburg.informatik.ultimate.logic.Util;


public class DnfTransformer extends TermTransformer {
	
	private final Script m_Script;

	
	
	public DnfTransformer(Script script) {
		super();
		m_Script = script;
	}

	@Override
	protected void convert(Term term) {
		assert term.getSort().getName().equals("Bool");
		if (term instanceof ApplicationTerm) {
			ApplicationTerm appTerm = (ApplicationTerm) term; 
			String functionName = appTerm.getFunction().getName();
			if (functionName.equals("and")) {
				super.convert(term);
			} else if (functionName.equals("or")) {
				super.convert(term);
			} else if (functionName.equals("not")) {
				assert false;
			} else if (functionName.equals("=>")) {
				Term[] params = appTerm.getParameters();
				Term[] newParams = new Term[params.length];
				newParams[0] = Util.not(m_Script, params[0]); 
				for (int i=0; i<params.length; i++) {
					newParams[i] = params[i];
				}
				super.convert(Util.or(m_Script, newParams));
			} else {
				
			}
			
		}
		// TODO Auto-generated method stub
		super.convert(term);
	}

	@Override
	public void convertApplicationTerm(ApplicationTerm appTerm, Term[] newArgs) {
		// TODO Auto-generated method stub
		super.convertApplicationTerm(appTerm, newArgs);
	}

}
