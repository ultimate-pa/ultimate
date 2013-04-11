package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;

/**
 * Operation that returns the number of states of a nested word automaton.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class NumberOfStates<LETTER, STATE> implements IOperation {
	
	INestedWordAutomaton<LETTER, STATE> m_Nwa;
	
	public NumberOfStates(INestedWordAutomaton<LETTER, STATE> nwa) {
		m_Nwa = nwa;
	}

	@Override
	public String operationName() {
		return "numberOfStates";
	}

	@Override
	public String startMessage() {
		throw new UnsupportedOperationException();
	}

	@Override
	public String exitMessage() {
		throw new UnsupportedOperationException();
	}

	@Override
	public Integer getResult() throws OperationCanceledException {
		return m_Nwa.size();
	}

}
