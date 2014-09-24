package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.NestedWordAutomata;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;

public class MinimizeDfaHopcroft<LETTER, STATE> implements IOperation<LETTER, STATE> {

	private INestedWordAutomaton<LETTER, STATE> m_Result;
	
	private INestedWordAutomaton<LETTER, STATE> m_operand;
	
	@Override
	public String operationName() {
		return "minimizeDfaHopcroft";
	}

	@Override
	public String startMessage() {
		return "Starting minimization";
	}

	@Override
	public String exitMessage() {
		return "Finished minimization";
	}

	@Override
	public Object getResult() throws OperationCanceledException {
		// TODO Auto-generated method stub
		return m_Result;
	}

	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// TODO check result.
		return false;
	}

}
