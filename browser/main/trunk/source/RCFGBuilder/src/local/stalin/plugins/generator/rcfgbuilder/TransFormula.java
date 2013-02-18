package local.stalin.plugins.generator.rcfgbuilder;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

import local.stalin.logic.Formula;
import local.stalin.logic.TermVariable;

/**
 * Represents the transition of a program or a transition system as an SMT
 * formula. The formula denotes a binary relation of this-state/next-state
 * pairs, where we consider a state as a variable assignment.
 * The variables that describe the "this-state"s are given as a set of strings,
 * stored as the keySet of the Map m_InVars. m_InVars maps to each of these
 * variables a corresponding TermVariable in the formula. 
 * The variables that describe the "next-state"s are given as a set of strings,
 * stored as the keySet of the Map m_OutVars. m_InVars maps to each of these
 * variables a corresponding TermVariable in the formula.
 * All TermVariables that occur in the formula are stored in the Set m_Vars.
 * The names of all variables that are assigned/updated by this transition are
 * stored in m_AssignedVars (this information is obtained from m_InVars and 
 * m_OutVars).
 * 
 * Additionally TransitionFormula takes care of a special BoogiePL feature.
 * There, every variable can occur twice. Once in an "old context", and once in
 * the normal context. A global variable in the old context refers to the
 * condition of this variable at the beginning of a procedure.
 * All variables that occur in m_InVars and m_OutVars refer to the variables in
 * the normal context. The Map m_OldVars maps a variable v to the TermVariable,
 * that represents the "old context" version of v in the formula.   
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class TransFormula {
	private final Formula m_Formula;
	private final Set<TermVariable> m_Vars;
	private final Map<String, TermVariable> m_InVars;
	private final Map<String, TermVariable> m_OutVars;
	private final Map<String, TermVariable> m_OldVars;
	private final Set<String> m_AssignedVars;
	
	public TransFormula(Formula formula,
			Map<String, TermVariable> inVars,
			Map<String, TermVariable> outVars,
			Map<String, TermVariable> oldVars,
			Set<TermVariable> vars
	) {
		m_Formula = formula;
		m_InVars = inVars;
		m_OutVars = outVars;
		m_OldVars = oldVars;
		m_Vars = vars;
		
		// compute the assigned/updated variables. A variable is updated by this
		// transition if it occurs as outVar and 
		// - it does not occur as inVar 
		// - or the inVar is represented by a different TermVariable 
		m_AssignedVars = new HashSet<String>();
		for (String var: outVars.keySet()) {
			assert (outVars.get(var) != null);
			if (outVars.get(var) != inVars.get(var)) {
				m_AssignedVars.add(var);
			}
		}
	}

	/**
	 * @return the m_Assertion
	 */
	public Formula getFormula() {
		return m_Formula;
	}

	/**
	 * @return the m_Vars
	 */
	public Set<TermVariable> getVars() {
		return m_Vars;
	}

	/**
	 * @return the m_InVars
	 */
	public Map<String, TermVariable> getInVars() {
		return m_InVars;
	}

	/**
	 * @return the m_OutVars
	 */
	public Map<String, TermVariable> getOutVars() {
		return m_OutVars;
	}

	/**
	 * @return the m_OldVars
	 */
	public Map<String, TermVariable> getOldVars() {
		return m_OldVars;
	}
	
	/**
	 * @return the m_AssignedVars
	 */
	public Set<String> getAssignedVars() {
		return m_AssignedVars;
	}

	@Override
	public String toString() {
		return "Formula: "+m_Formula + 
				"  Vars: " + m_Vars + 
				"  InVars " + m_InVars + 
				"  OutVars" + m_OutVars +
				"  OldVars" + m_OldVars +
				"  AssignedVars" + m_AssignedVars;
	}
	
	


	
	 

}
