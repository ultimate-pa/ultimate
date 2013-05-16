package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DeletedStatesAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class RemoveDeadEnds<LETTER,STATE> implements IOperation {
	
	private final INestedWordAutomaton<LETTER,STATE> m_Input;
	private final ReachableStatesAutomaton<LETTER,STATE> m_Reach;
	private final INestedWordAutomaton<LETTER,STATE> m_Result;

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	/**
	 * Given an INestedWordAutomaton nwa return a nested word automaton that has
	 * the same states, but all states that are not reachable or dead ends are
	 * omitted. (A dead end is a state from which no accepting state can be 
	 * reached).
	 * Each state of the result also occurred in the input. Only the auxiliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws OperationCanceledException
	 */
	public RemoveDeadEnds(INestedWordAutomaton<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_Reach = new ReachableStatesAutomaton<LETTER, STATE>(m_Input);
		m_Result = new DeletedStatesAutomaton<LETTER, STATE>(m_Reach);
		s_Logger.info(exitMessage());
		assert (checkResult());
	}
	

	@Override
	public String operationName() {
		return "removeDeadEnds";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ m_Input.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Reach.sizeInformation();
	}


	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() throws OperationCanceledException {
		return m_Result;
	}
	
	public boolean checkResult() throws OperationCanceledException {
		boolean correct = true;
		correct &= ResultChecker.minimize(m_Input, m_Result); 
//		correct &= (new IsIncluded<LETTER, STATE>(m_Input, m_Result)).getResult();
//		correct &= (new IsIncluded<LETTER, STATE>(m_Result, m_Input)).getResult();
		return correct;
	}



}