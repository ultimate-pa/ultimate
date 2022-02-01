/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2014-2015 Markus Pomrehn
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AutomataScriptParser plug-in.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AutomataScriptParser plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AutomataScriptParser plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AutomataScriptParser plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AutomataScriptParser plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.source.automatascriptparser.AST;

import java.util.List;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class AlternatingAutomatonAST extends AutomatonAST{

	private List<String> alphabet;
	private List<String> states;
	private List<String> finalStates;
	private Map<Pair<String, String>, Set<String>> transitions;
	private String acceptingFunction;
	private boolean isReversed;
	
	public AlternatingAutomatonAST(final ILocation loc, final String name){
		super(loc, name);
//		mName = name;
	}
	
	public void setAlphabet(final List<String> alphabet){
		this.alphabet = alphabet;
	}

	public List<String> getAlphabet(){
		return alphabet;
	}
	
	public void setStates(final List<String> states){
		this.states = states;
	}
	
	public List<String> getStates(){
		return states;
	}
	
	public void setFinalStates(final List<String> finalStates){
		this.finalStates = finalStates;
	}

	public List<String> getFinalStates() {
		return finalStates;
	}
	
	public void setTransitions(final Map<Pair<String, String>, Set<String>> transitions){
		this.transitions = transitions;
	}
	
	public Map<Pair<String, String>, Set<String>> getTransitions(){
		return transitions;
	}
	
	public void setAcceptingFunction(final String acceptingFunction){
		this.acceptingFunction = acceptingFunction;
	}
	
	public String getAcceptingFunction(){
		return acceptingFunction;
	}
	
	public void setReversed(final boolean isReversed){
		this.isReversed = isReversed;
	}
	
	public boolean isReversed(){
		return isReversed;
	}
	
	@Override
	public String toString(){
		final StringBuilder builder = new StringBuilder();
		builder.append("AlternatingAutomaton(" + mName + "): + [");
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
