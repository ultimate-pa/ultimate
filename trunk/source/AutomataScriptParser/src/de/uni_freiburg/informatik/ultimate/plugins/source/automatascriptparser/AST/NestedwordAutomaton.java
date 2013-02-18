/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;


import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionList.Pair;



/**
 * @author musab@informatik.uni-freiburg.de
 *
 */
public class NestedwordAutomaton extends Automaton {

	/**
	 * 
	 */
	private static final long serialVersionUID = 2260897609736623517L;
	
	private List<String> m_CallAlphabet;
	private List<String> m_InternalAlphabet;
	private List<String> m_ReturnAlphabet;
	
	private List<String> m_States;
	private List<String> m_InitialStates;
	private List<String> m_FinalStates;
	
	private Map<Pair<String, String>, String> m_InternalTransitions;
	private Map<Pair<String, String>, String> m_CallTransitions;
	private Map<Pair<String, String>, Pair<String, String>> m_ReturnTransitions;
	
	public NestedwordAutomaton(String name) {
		m_CallAlphabet = new ArrayList<String>();
		m_InternalAlphabet = new ArrayList<String>();
		m_ReturnAlphabet = new ArrayList<String>();
		m_States = new ArrayList<String>();
		m_InitialStates = new ArrayList<String>();
		m_FinalStates = new ArrayList<String>();
		m_InternalTransitions = new HashMap<Pair<String,String>, String>();
		m_CallTransitions = new HashMap<Pair<String,String>, String>();
		m_ReturnTransitions = new HashMap<Pair<String, String>, Pair<String, String>>();
		m_Name = name;
		
	}

	public List<String> getCallAlphabet() {
		return m_CallAlphabet;
	}

	public void setCallAlphabet(List<String> m_CallAlphabet) {
		if (m_CallAlphabet != null)
			this.m_CallAlphabet = m_CallAlphabet;
	}

	public List<String> getInternalAlphabet() {
		return m_InternalAlphabet;
	}

	public void setInternalAlphabet(List<String> m_InternalAlphabet) {
		if (m_InternalAlphabet != null)
			this.m_InternalAlphabet = m_InternalAlphabet;
	}

	public List<String> getReturnAlphabet() {
		return m_ReturnAlphabet;
	}

	public void setReturnAlphabet(List<String> m_ReturnAlphabet) {
		if (m_ReturnAlphabet != null)
			this.m_ReturnAlphabet = m_ReturnAlphabet;
	}
	
	public void setStates(List<String> states) {
		if (states != null)
			m_States = states;
	}
	
	public void setInitialStates(List<String> initStates) {
		if (initStates != null)
			m_InitialStates = initStates;
	}
	public void setFinalStates(List<String> finStates) {
		if (finStates != null)
			m_FinalStates = finStates;
	}

	public List<String> getStates() {
		return m_States;
	}

	public List<String> getInitialStates() {
		return m_InitialStates;
	}

	public List<String> getFinalStates() {
		return m_FinalStates;
	}

	
	public Map<Pair<String, String>, String> getInternalTransitions() {
		return m_InternalTransitions;
	}

	public void setInternalTransitions(TransitionList internalTransitions) {
		if (internalTransitions != null)
			this.m_InternalTransitions = internalTransitions.getTransitions();
	}

	public Map<Pair<String, String>, String> getCallTransitions() {
		return m_CallTransitions;
	}

	public void setCallTransitions(TransitionList callTransitions) {
		if (callTransitions != null)
			this.m_CallTransitions = callTransitions.getTransitions();
	}

	public Map<Pair<String, String>, Pair<String, String>> getReturnTransitions() {
		return m_ReturnTransitions;
	}

	public void setReturnTransitions(TransitionList returnTransitions) {
		if (returnTransitions != null)
			this.m_ReturnTransitions = returnTransitions.getReturnTransitions();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("NestedwordAutomaton(" + m_Name + "): " + "[#call_alph: ");
		builder.append(m_CallAlphabet.size());
		builder.append(" #int_alph: ");
		builder.append(m_InternalAlphabet.size());
		builder.append(" #return_alph: ");
		builder.append(m_ReturnAlphabet.size());
		builder.append(" #States: ");
		builder.append(m_States.size());
		builder.append(" #init_states: ");
		builder.append(m_InitialStates.size());
		builder.append(" #final_states: ");
		builder.append(m_FinalStates.size());
		builder.append(" #int_trans: ");
		builder.append(m_InternalTransitions.size());
		builder.append(" #call_trans: ");
		builder.append(m_CallTransitions.size());
		builder.append(" #ret_trans: ");
		builder.append(m_ReturnTransitions.size());
		builder.append("]");
		return builder.toString();
	}

	

}
