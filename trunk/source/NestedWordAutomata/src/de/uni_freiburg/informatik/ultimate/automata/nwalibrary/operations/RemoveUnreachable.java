package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.ReachableStatesAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class RemoveUnreachable<LETTER,STATE> implements IOperation {
	
	private final INestedWordAutomaton<LETTER,STATE> m_Input;
	private final INestedWordAutomaton<LETTER,STATE> m_Result;

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	/**
	 * Given an INestedWordAutomaton nwa return a NestedWordAutomaton that has
	 * the same states, but all states that are not reachable are omitted.
	 * Each state of the result also occurred in the input. Only the auxilliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws OperationCanceledException
	 */
	public RemoveUnreachable(INestedWordAutomaton<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_Result = new ReachableStatesAutomaton<LETTER, STATE>(m_Input);
		s_Logger.info(exitMessage());
	}
	

	@Override
	public String operationName() {
		return "removeUnreachable";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ m_Input.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_Result.sizeInformation();
	}


	@Override
	public Object getResult() throws OperationCanceledException {
		return m_Result;
	}



}