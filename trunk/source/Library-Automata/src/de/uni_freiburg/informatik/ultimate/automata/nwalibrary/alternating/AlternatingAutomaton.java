/*
 * Copyright (C) 2015 Carl Kuesters
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class AlternatingAutomaton<LETTER, STATE> implements IAutomaton<LETTER, STATE>{

	public AlternatingAutomaton(Set<LETTER> alphabet, StateFactory<STATE> stateFactory){
		this.alphabet = alphabet;
		this.stateFactory = stateFactory;
	}
	private Set<LETTER> alphabet;
	private StateFactory<STATE> stateFactory;
	private ArrayList<STATE> states = new ArrayList<STATE>();
	private HashMap<STATE, Integer> statesIndices = new HashMap<STATE, Integer>();
	private HashMap<LETTER, BooleanExpression[]> transitionFunction = new HashMap<LETTER, BooleanExpression[]>();
	private BooleanExpression acceptingFunction;
	private BitSet finalStatesBitVector = new BitSet();
	private boolean isReversed;
	
	public void addState(STATE state){
		if(!states.contains(state)){
			int stateIndex = states.size();
			states.add(state);
			statesIndices.put(state, stateIndex);
		}
	}
	
	public void addTransition(LETTER letter, STATE state, BooleanExpression booleanExpression){
		BooleanExpression[] letterTransitions = transitionFunction.get(letter);
		if(letterTransitions == null){
			letterTransitions = new BooleanExpression[64];
			transitionFunction.put(letter, letterTransitions);
		}
		int stateIndex = getStateIndex(state);
		if(letterTransitions[stateIndex] == null){
			letterTransitions[stateIndex] = booleanExpression;
		}
		else{
			letterTransitions[stateIndex].addConjunction(booleanExpression);
		}
	}
	
	public void addAcceptingConjunction(BooleanExpression booleanExpression){
		if(acceptingFunction == null){
			acceptingFunction = booleanExpression;
		}
		else{
			acceptingFunction.addConjunction(booleanExpression);
		}
	}
	
	public BooleanExpression generateCube(STATE[] resultStates, STATE[] negatedResultStates){
		BitSet alpha = new BitSet(states.size());
		BitSet beta = new BitSet(states.size());
		for(STATE resultState : resultStates){
			int stateIndex = getStateIndex(resultState);
			alpha.set(stateIndex);
			beta.set(stateIndex);
		}
		for(STATE resultState : negatedResultStates){
			int stateIndex = getStateIndex(resultState);
			alpha.set(stateIndex);
		}
		return new BooleanExpression(alpha, beta);
	}
	
	public void setStateFinal(STATE state){
		int stateIndex = getStateIndex(state);
		finalStatesBitVector.set(stateIndex);
	}
	
	public boolean isStateFinal(STATE state){
		int stateIndex = getStateIndex(state);
		return finalStatesBitVector.get(stateIndex);
	}
	
	public boolean accepts(Word<LETTER> word){
		BitSet resultingStates = (BitSet) finalStatesBitVector.clone();
		if(isReversed){
			for(int i=0;i<word.length();i++){
				resolveLetter(word.getSymbol(i), resultingStates);
			}
		}
		else{
			for(int i=(word.length() - 1);i>=0;i--){
				resolveLetter(word.getSymbol(i), resultingStates);
			}
		}
		return acceptingFunction.getResult(resultingStates);
	}
	
	public void resolveLetter(LETTER letter, BitSet currentStates){
		BooleanExpression[] letterTransitions = transitionFunction.get(letter);
		if(letterTransitions != null){
			BitSet tmpCurrentStates = (BitSet) currentStates.clone();
			for(int i=0;i<states.size();i++){
				boolean result = ((letterTransitions[i] != null)?letterTransitions[i].getResult(tmpCurrentStates):false);
				currentStates.set(i, result);
			}
		}
		else{
			currentStates.clear();
		}
	}
	
	public ArrayList<STATE> getStates(){
		return states;
	}
	
	public int getStateIndex(STATE state){
		return statesIndices.get(state);
	}
	
	public HashMap<LETTER, BooleanExpression[]> getTransitionFunction(){
		return transitionFunction;
	}
	
	public BooleanExpression getAcceptingFunction(){
		return acceptingFunction;
	}
	
	public BitSet getFinalStatesBitVector(){
		return finalStatesBitVector;
	}
	
	public void setReversed(boolean isReversed){
		this.isReversed = isReversed;
	}
	
	public boolean isReversed(){
		return isReversed;
	}

	@Override
	public Set<LETTER> getAlphabet(){
		return alphabet;
	}

	@Override
	public StateFactory<STATE> getStateFactory(){
		return stateFactory;
	}

	@Override
	public int size(){
		return states.size();
	}

	@Override
	public String sizeInformation(){
		return "Number of states";
	}
	
	@Override
	public String toString(){
		String text = "[AlternatingAutomaton\n\tAlphabet = {";
		Iterator<LETTER> letterIterator = alphabet.iterator();
		int r = 0;
		while(letterIterator.hasNext()){
			if(r != 0){
				text += ", ";
			}
			text += letterIterator.next();
			r++;
		}
		text += "}\n\tStates = {";
		for(int i=0;i<states.size();i++){
			if(i != 0){
				text += ", ";
			}
			text += states.get(i);
		}
		text += "}\n\tFinalStates = {";
		r = 0;
		for(int i=0;i<states.size();i++){
			if(finalStatesBitVector.get(i)){
				if(r != 0){
					text += ", ";
				}
				text += states.get(i);
				r++;
			}
		}
		text += "}\n\tAcceptingFunction = " + acceptingFunction.toString(states) + "\n\tTransistions = {\n";
		r = 0;
		for(Entry<LETTER, BooleanExpression[]> entry : transitionFunction.entrySet()){
			text += "\t\t" + entry.getKey() + " => {\n";
			int z = 0;
			for(int i=0;i<states.size();i++){
				if(entry.getValue()[i] != null){
					if(z != 0){
						text += ",\n";
					}
					text += "\t\t\t" + states.get(i) + " => " + entry.getValue()[i].toString(states);
					z++;
				}
			}
			text += "\n\t\t}";
			if(r != (transitionFunction.size() - 1)){
				text += ",";
			}
			text += "\n";
			r++;
		}
		text += "\t}\n]";
		return text;
	}
}
