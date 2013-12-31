package de.uni_freiburg.informatik.ultimate.plugins.analysis.lassoranker;

import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.logic.Term;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * TODO: documentation
 * 
 * @author Matthias Heizmann
 *
 */
public class AuxVarManager {
	private final Script m_Script;
	private int m_ConstructedAuxVars = 0;
	private final Map<TermVariable, Term> m_AuxVar2Definition = 
			new HashMap<TermVariable, Term>();
	
	public AuxVarManager(Script script) {
		super();
		m_Script = script;
	}

	public TermVariable constructAuxVar(String prefix, Term definition) {
		String varname = prefix + "_" + m_ConstructedAuxVars;
		Sort sort = definition.getSort();
		TermVariable auxVar = m_Script.variable(varname, sort);
		m_ConstructedAuxVars++;
		m_AuxVar2Definition.put(auxVar, definition);
		return auxVar;
	}
	
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(m_AuxVar2Definition.keySet());
	}
	
	public Term getDefinition(TermVariable tv) {
		Term result = m_AuxVar2Definition.get(tv);
		if (result == null) {
			throw new IllegalArgumentException("unknown variable");
		}
		return result;
	}

}
