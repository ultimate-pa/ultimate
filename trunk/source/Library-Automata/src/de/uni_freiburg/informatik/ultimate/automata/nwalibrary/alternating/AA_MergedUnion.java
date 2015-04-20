package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.HashMap;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class AA_MergedUnion<LETTER, STATE> implements IOperation<LETTER, STATE>{

	public AA_MergedUnion(AlternatingAutomaton<LETTER, STATE> automaton1, AlternatingAutomaton<LETTER, STATE> automaton2){
		assert automaton1.getAlphabet().equals(automaton2.getAlphabet());
		assert (automaton1.isReversed() == automaton2.isReversed());
		resultAutomaton = new AlternatingAutomaton<>(automaton1.getAlphabet(), automaton1.getStateFactory());
		HashMap<Integer, Integer> shiftMap1 = new HashMap<>();
		HashMap<Integer, Integer> shiftMap2 = new HashMap<>();
		for(STATE state : automaton1.getStates()){
			resultAutomaton.addState(state);
			shiftMap1.put(automaton1.getStateIndex(state), resultAutomaton.getStateIndex(state));
			if(automaton1.isStateFinal(state)){
				resultAutomaton.setStateFinal(state);
			}
		}
		for(STATE state : automaton2.getStates()){
			resultAutomaton.addState(state);
			shiftMap2.put(automaton2.getStateIndex(state), resultAutomaton.getStateIndex(state));
			if(automaton2.isStateFinal(state)){
				resultAutomaton.setStateFinal(state);
			}
		}
		int newSize = resultAutomaton.getStates().size();
		for(Entry<LETTER, BooleanExpression[]> entry : automaton1.getTransitionFunction().entrySet()){
			for(int i=0;i<automaton1.getStates().size();i++){
				if(entry.getValue()[i] != null){
					resultAutomaton.addTransition(
							entry.getKey(), 
							automaton1.getStates().get(i), 
							entry.getValue()[i].cloneShifted(shiftMap1, newSize));
				}
			}
		}
		for(Entry<LETTER, BooleanExpression[]> entry : automaton2.getTransitionFunction().entrySet()){
			for(int i=0;i<automaton2.getStates().size();i++){
				if(entry.getValue()[i] != null){
					resultAutomaton.addTransition(
							entry.getKey(), 
							automaton2.getStates().get(i), 
							entry.getValue()[i].cloneShifted(shiftMap2, newSize));
				}
			}
		}
		resultAutomaton.addAcceptingConjunction(automaton1.getAcceptingFunction().cloneShifted(shiftMap1, newSize));
		resultAutomaton.addAcceptingConjunction(automaton2.getAcceptingFunction().cloneShifted(shiftMap2, newSize));
		resultAutomaton.setReversed(automaton1.isReversed());
	}
	private AlternatingAutomaton<LETTER, STATE> resultAutomaton;

	@Override
	public String operationName(){
		return "AA_MergedUnion";
	}

	@Override
	public String startMessage(){
		return "Start: " + operationName();
	}

	@Override
	public String exitMessage(){
		return "Exit: " + operationName();
	}

	@Override
	public AlternatingAutomaton<LETTER, STATE> getResult() throws OperationCanceledException{
		return resultAutomaton;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException{
		return true;
	}
}
