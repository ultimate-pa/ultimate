package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class AA_Union<LETTER, STATE> implements IOperation<LETTER, STATE>{

	public AA_Union(AlternatingAutomaton<LETTER, STATE> automaton1, AlternatingAutomaton<LETTER, STATE> automaton2){
		assert automaton1.getAlphabet().equals(automaton2.getAlphabet());
		resultAutomaton = new AlternatingAutomaton<>(automaton1.getAlphabet(), automaton1.getStateFactory());
		for(STATE state : automaton1.getStates()){
			resultAutomaton.addState(state);
			if(automaton1.isStateFinal(state)){
				resultAutomaton.setStateFinal(state);
			}
		}
		for(STATE state : automaton2.getStates()){
			resultAutomaton.addState(state);
			if(automaton2.isStateFinal(state)){
				resultAutomaton.setStateFinal(state);
			}
		}
		for(Entry<LETTER, BooleanExpression[]> entry : automaton1.getTransitionFunction().entrySet()){
			for(int i=0;i<automaton1.getStates().size();i++){
				resultAutomaton.addTransition(entry.getKey(), automaton1.getStates().get(i), entry.getValue()[i]);
			}
		}
		for(Entry<LETTER, BooleanExpression[]> entry : automaton2.getTransitionFunction().entrySet()){
			for(int i=0;i<automaton2.getStates().size();i++){
				resultAutomaton.addTransition(entry.getKey(), automaton2.getStates().get(i), entry.getValue()[i]);
			}
		}
		resultAutomaton.addAcceptingConjunction(automaton1.getAcceptingFunction());
		resultAutomaton.addAcceptingConjunction(automaton2.getAcceptingFunction().cloneShifted(automaton1.getStates().size()));
	}
	private AlternatingAutomaton<LETTER, STATE> resultAutomaton;

	@Override
	public String operationName(){
		return "AA_Union";
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
