package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionListAST.Pair;

// Test
public class AlternatingAutomatonAST extends AutomatonAST {

	private List<String> m_Alphabet;
	
	
	private List<String> m_ExStates;
	private List<String> m_UniStates;
	private List<String> m_InitialStates;
	private List<String> m_FinalStates;
	
	private Map<Pair<String, String>, Set<String>> m_transitions;
	
	public AlternatingAutomatonAST(ILocation loc, String name) {
		super(loc);
		m_Alphabet = new ArrayList<String>();
		m_ExStates = new ArrayList<String>();
		m_UniStates = new ArrayList<String>();
		m_InitialStates = new ArrayList<String>();
		m_FinalStates = new ArrayList<String>();
		m_transitions = new HashMap<Pair<String,String>, Set<String>>();
		m_Name = name;
		
	}

	public List<String> getAlphabet() {
		return m_Alphabet;
	}

	public void setAlphabet(List<String> m_Alphabet) {
		if (m_Alphabet != null)
			this.m_Alphabet = m_Alphabet;
	}
	
	public void setExistentialStates(List<String> exStates) {
		if (exStates != null)
			m_ExStates = exStates;
	}
	
	public void setUniversalStates(List<String> uniStates) {
		if (uniStates != null)
			m_UniStates = uniStates;
	}
	
	public void setInitialStates(List<String> initStates) {
		if (initStates != null)
			m_InitialStates = initStates;
	}
	public void setFinalStates(List<String> finStates) {
		if (finStates != null)
			m_FinalStates = finStates;
	}

	public List<String> getExStates() {
		return m_ExStates;
	}
	
	public List<String> getUniStates() {
		return m_UniStates;
	}

	public List<String> getInitialStates() {
		return m_InitialStates;
	}

	public List<String> getFinalStates() {
		return m_FinalStates;
	}

	
	public Map<Pair<String, String>, Set<String>> getTransitions() {
		return m_transitions;
	}

	public void setTransitions(TransitionListAST transitions) {
		if (transitions != null)
			this.m_transitions = transitions.getTransitions();
	}

	@Override
	public String toString() {
		StringBuilder builder = new StringBuilder();
		builder.append("NestedwordAutomaton(" + m_Name + "): + [");
		builder.append(" #int_alph: ");
		builder.append(m_Alphabet.size());
		builder.append(" #ExStates: ");
		builder.append(m_ExStates.size());
		builder.append(" #UniStates: ");
		builder.append(m_UniStates.size());
		builder.append(" #init_states: ");
		builder.append(m_InitialStates.size());
		builder.append(" #final_states: ");
		builder.append(m_FinalStates.size());
		builder.append(" #int_trans: ");
		builder.append(m_transitions.size());
		builder.append("]");
		return builder.toString();
	}

	

}
