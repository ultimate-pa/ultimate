package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import java.util.BitSet;
import java.util.Collections;
import java.util.LinkedList;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating.AlternatingAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

public class AA_DeterminizeReversed<LETTER> implements IOperation<LETTER, BitSet>{

	public AA_DeterminizeReversed(IUltimateServiceProvider ultimateServiceProvider, AlternatingAutomaton<LETTER, BitSet> alternatingAutomaton){
		resultAutomaton = new NestedWordAutomaton<LETTER, BitSet>(
				ultimateServiceProvider,
				alternatingAutomaton.getAlphabet(),
				Collections.<LETTER>emptySet(),
				Collections.<LETTER>emptySet(),
				alternatingAutomaton.getStateFactory()
			);
		LinkedList<BitSet> newStates = new LinkedList<BitSet>();
		newStates.add(alternatingAutomaton.getFinalStatesBitVector());
		while(!newStates.isEmpty()){
			BitSet state = newStates.getFirst();
			boolean isInitial = (state == alternatingAutomaton.getFinalStatesBitVector());
			boolean isFinal = alternatingAutomaton.getAcceptingFunction().getResult(state);
			resultAutomaton.addState(isInitial, isFinal, state);
			for(LETTER letter : alternatingAutomaton.getAlphabet()){
				BitSet nextState = (BitSet) state.clone();
				alternatingAutomaton.resolveLetter(letter, nextState);
				resultAutomaton.addInternalTransition(state, letter, nextState);
				if(!resultAutomaton.getStates().contains(nextState)){
					if(!newStates.contains(nextState)){
						newStates.add(nextState);
					}
				}
			}
			newStates.removeFirst();
		}
	}
	private NestedWordAutomaton<LETTER, BitSet> resultAutomaton;
	
	@Override
	public String operationName(){
		return "AA_DeterminizeReversed";
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
	public NestedWordAutomaton<LETTER, BitSet> getResult() throws AutomataLibraryException{
		return resultAutomaton;
	}

	@Override
	public boolean checkResult(StateFactory<BitSet> stateFactory) throws AutomataLibraryException{
		return true;
	}
}
