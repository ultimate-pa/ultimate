package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class RemoveUnreachable<LETTER,STATE> implements IOperation {
	
	private final INestedWordAutomatonSimple<LETTER,STATE> m_Input;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Result;

	private static Logger s_Logger = UltimateServices.getInstance().getLogger(
			Activator.PLUGIN_ID);

	/**
	 * Given an INestedWordAutomaton nwa return a NestedWordAutomaton that has
	 * the same states, but all states that are not reachable are omitted.
	 * Each state of the result also occurred in the input. Only the auxiliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws OperationCanceledException
	 */
	public RemoveUnreachable(INestedWordAutomatonSimple<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_Result = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Input);
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
	public NestedWordAutomatonReachableStates<LETTER,STATE> getResult() throws OperationCanceledException {
		if (m_Input instanceof INestedWordAutomatonOldApi) {
			assert checkResult();
		}
		return m_Result;
	}

	public boolean checkResult() throws OperationCanceledException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
//		correct &= (ResultChecker.nwaLanguageInclusion(m_Input, m_Result) == null);
//		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, m_Input) == null);
		assert correct;
		DoubleDeckerAutomaton<LETTER, STATE> reachalbeStatesCopy = 
				(DoubleDeckerAutomaton<LETTER, STATE>) (new ReachableStatesCopy(
						(INestedWordAutomatonOldApi) m_Input, false, false, false, false)).getResult();
//		correct &= ResultChecker.isSubset(reachalbeStatesCopy.getStates(),m_Result.getStates());
		assert correct;
//		correct &= ResultChecker.isSubset(m_Result.getStates(),reachalbeStatesCopy.getStates());
		assert correct;
		for (STATE state : reachalbeStatesCopy.getStates()) {
			Set<STATE> rCSdownStates = reachalbeStatesCopy.getDownStates(state);
			Set<STATE> rCAdownStates = m_Result.getDownStates(state);
			correct &= ResultChecker.isSubset(rCAdownStates, rCSdownStates);
			assert correct;
			correct &= ResultChecker.isSubset(rCSdownStates, rCAdownStates);
			assert correct;
		}
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(operationName() + "Failed", "", m_Input);
		}
		s_Logger.info("Finished testing correctness of " + operationName());
		return correct;
	}

}