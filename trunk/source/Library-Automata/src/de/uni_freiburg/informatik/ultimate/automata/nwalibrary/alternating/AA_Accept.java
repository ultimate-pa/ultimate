package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.alternating;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.Word;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class AA_Accept<LETTER,STATE> implements IOperation<LETTER,STATE>{
	
	public AA_Accept(AlternatingAutomaton<LETTER,STATE> alternatingAutomaton, Word<LETTER> word) throws OperationCanceledException{
		isAccepted = alternatingAutomaton.accepts(word);
	}
	private boolean isAccepted;
	
	@Override
	public String operationName(){
		return "AA_Accept";
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
	public Boolean getResult(){
		return isAccepted;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataLibraryException{
		return true;
	}
}

