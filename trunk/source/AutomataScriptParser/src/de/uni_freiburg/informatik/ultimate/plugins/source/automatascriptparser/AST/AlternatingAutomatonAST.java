package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.model.location.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST.TransitionListAST.Pair;

public class AlternatingAutomatonAST extends AutomatonAST{

	private List<String> alphabet;
	private List<String> states;
	private List<String> finalStates;
	private Map<Pair<String, String>, Set<String>> transitions;
	private String acceptingFunction;
	
	public AlternatingAutomatonAST(ILocation loc, String name){
		super(loc);
		m_Name = name;
	}
	
	public void setAlphabet(List<String> alphabet){
		this.alphabet = alphabet;
	}

	public List<String> getAlphabet(){
		return alphabet;
	}
	
	public void setStates(List<String> states){
		this.states = states;
	}
	
	public List<String> getStates(){
		return states;
	}
	
	public void setFinalStates(List<String> finalStates){
		this.finalStates = finalStates;
	}

	public List<String> getFinalStates() {
		return finalStates;
	}
	
	public void setTransitions(Map<Pair<String, String>, Set<String>> transitions){
		this.transitions = transitions;
	}
	
	public Map<Pair<String, String>, Set<String>> getTransitions(){
		return transitions;
	}
	
	public void setAcceptingFunction(String acceptingFunction){
		this.acceptingFunction = acceptingFunction;
	}
	
	public String getAcceptingFunction(){
		return acceptingFunction;
	}
	
	@Override
	public String toString(){
		StringBuilder builder = new StringBuilder();
		builder.append("AlternatingAutomaton(" + m_Name + "): + [");
		builder.append(" #int_alph: ");
		builder.append(alphabet.size());
		builder.append(" #States: ");
		builder.append(states.size());
		builder.append(" #Transitions: ");
		builder.append(transitions.size());
		builder.append("]");
		return builder.toString();
	}
}
