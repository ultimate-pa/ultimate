package de.uni_freiburg.informatik.ultimate.modelcheckerutils.boogie;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;
import de.uni_freiburg.informatik.ultimate.model.boogie.BoogieVar;

public class VariableManager {
	private final MultiElementCounter<BoogieVar> m_TvForBoogieVarCounter = 
			new MultiElementCounter<BoogieVar>();
	private final Script m_Script;
	
	VariableManager(Script script) {
		m_Script = script;
	}
	
	TermVariable constructFreshTermVariable(BoogieVar bv) {
		final String name = bv.toString();
		final Integer newIndex = m_TvForBoogieVarCounter.increase(bv);
		final Sort sort = bv.getTermVariable().getSort();
		TermVariable result = m_Script.variable(
				"v_" + name + "_" + newIndex, sort);
		return result;
	}
	
	

}
