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
 * Object that creates unique auxiliary TermVariables. For each auxiliary you
 * have to provide a Term, called the definition of this auxiliary TermVariable.
 * The constructed auxiliary TermVariable has the same Sort as its definition.
 * This object can return all auxiliary TermVariables constructed so far and
 * provides a mapping from auxiliary TermVariables to their definitions.
 * 
 * TODO: At the moment the auxiliary TermVariables are only unique with respect
 * to other auxiliary TermVariables constructed by the same object.
 * In the future the auxiliary TermVariables will be unique with respect to
 * all TermVariables constructed for some Boogie2SMT object.
 * 
 * @author Matthias Heizmann
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

	
	/**
	 * Construct and return a unique auxiliary TermVariable with the given 
	 * prefix that has the same sort as the given Term definition. 
	 * Store that the returned auxiliary TermVariable was constructed for the
	 * given Term definition.
	 */
	public TermVariable constructAuxVar(String prefix, Term definition) {
		String varname = prefix + "_" + m_ConstructedAuxVars;
		Sort sort = definition.getSort();
		TermVariable auxVar = m_Script.variable(varname, sort);
		m_ConstructedAuxVars++;
		m_AuxVar2Definition.put(auxVar, definition);
		return auxVar;
	}
	
	
	/**
	 * Return an unmodifiable Set that contains all auxiliary TermVariables
	 * that have been constructed so far.
	 */
	public Set<TermVariable> getAuxVars() {
		return Collections.unmodifiableSet(m_AuxVar2Definition.keySet());
	}
	
	
	/**
	 * Given an auxiliary TermVariable constructed by this AuxVarManager, return
	 * the Term for which this auxiliary TermVariable was constructed. (We
	 * call this Term the definition of this auxiliary TermVariable).
	 */
	public Term getDefinition(TermVariable tv) {
		Term result = m_AuxVar2Definition.get(tv);
		if (result == null) {
			throw new IllegalArgumentException("unknown variable");
		}
		return result;
	}

}
