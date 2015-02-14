package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;
import java.util.HashMap;

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
	private long finalStatesBitVector;
	private boolean isReversed;
	
	public void addState(STATE state){
		int stateIndex = states.size();
		states.add(state);
		statesIndices.put(state, stateIndex);
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
	
	public BooleanExpression generateDisjunction(STATE[] resultStates, STATE[] negatedResultStates){
		long alpha = 0;
		long beta = 0;
		for(STATE resultState : resultStates){
			int stateIndex = getStateIndex(resultState);
			alpha = BitUtil.setBit(alpha, stateIndex);
			beta = BitUtil.setBit(beta, stateIndex);
		}
		for(STATE resultState : negatedResultStates){
			int stateIndex = getStateIndex(resultState);
			alpha = BitUtil.setBit(alpha, stateIndex);
		}
		return new BooleanExpression(alpha, beta);
	}
	
	public void setStateFinal(STATE state){
		int stateIndex = getStateIndex(state);
		finalStatesBitVector = BitUtil.setBit(finalStatesBitVector, stateIndex);
	}
	
	public boolean isStateFinal(STATE state){
		int stateIndex = getStateIndex(state);
		return BitUtil.getBit(finalStatesBitVector, stateIndex);
	}
	
	public boolean accepts(Word<LETTER> word){
		long resultingStates = finalStatesBitVector;
		if(isReversed){
			for(int i=0;i<word.length();i++){
				resultingStates = resolveLetter(word.getSymbol(i), resultingStates);
			}
		}
		else{
			for(int i=(word.length() - 1);i>=0;i--){
				resultingStates = resolveLetter(word.getSymbol(i), resultingStates);
			}
		}
		return acceptingFunction.getResult(resultingStates);
	}
	
	public long resolveLetter(LETTER letter, long currentStates){
		BooleanExpression[] letterTransitions = transitionFunction.get(letter);
		if(letterTransitions != null){
			long tmpCurrentStates = currentStates;
			for(int i=0;i<states.size();i++){
				boolean result = ((letterTransitions[i] != null)?letterTransitions[i].getResult(tmpCurrentStates):false);
				currentStates = BitUtil.setBit(currentStates, i, result);
			}
			return currentStates;
		}
		return 0;
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
	
	public long getFinalStatesBitVector(){
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
			if(BitUtil.getBit(finalStatesBitVector, i)){
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
