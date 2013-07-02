package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Collection;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.TransitionConsitenceCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class RemoveDeadEnds<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_Input;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> m_Reach;
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_Result;

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
	public RemoveDeadEnds(INestedWordAutomatonOldApi<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_Reach = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Input);
		m_Reach.computeDeadEnds();
		m_Result = new NestedWordAutomatonFilteredStates<LETTER, STATE>(m_Reach, m_Reach.getWithOutDeadEnds());
		s_Logger.info(exitMessage());
		assert (new TransitionConsitenceCheck<LETTER, STATE>(m_Result)).consistentForAll();
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
		return "Finished " + operationName() + " Reduced from " 
				+ m_Input.sizeInformation() + " to "
				+ m_Result.sizeInformation();
	}


	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult() throws OperationCanceledException {
		return m_Result;
	}
	
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws OperationCanceledException {
		s_Logger.info("Start testing correctness of " + operationName());
		boolean correct = true;
//		correct &= (ResultChecker.nwaLanguageInclusion(m_Input, m_Result) == null);
//		correct &= (ResultChecker.nwaLanguageInclusion(m_Result, m_Input) == null);
		assert correct;
		ReachableStatesCopy<LETTER, STATE> rsc = (new ReachableStatesCopy<LETTER, STATE>(m_Input, false, false, false, false));
//		Set<UpDownEntry<STATE>> rsaEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : m_Reach.getRemovedUpDownEntry()) {
//			rsaEntries.add(rde);
//		}
//		Set<UpDownEntry<STATE>> rscEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : rsc.getRemovedUpDownEntry()) {
//			rscEntries.add(rde);
//		}
//		correct &= ResultChecker.isSubset(rsaEntries,rscEntries);
//		assert correct;
//		correct &= ResultChecker.isSubset(rscEntries,rsaEntries);
//		assert correct;
		rsc.removeDeadEnds();
		DoubleDeckerAutomaton<LETTER, STATE> reachalbeStatesCopy = (DoubleDeckerAutomaton<LETTER, STATE>) rsc.getResult();
		correct &= m_Result.getStates().isEmpty() || ResultChecker.isSubset(reachalbeStatesCopy.getStates(),m_Result.getStates());
		assert correct;
		correct &= ResultChecker.isSubset(m_Result.getStates(),reachalbeStatesCopy.getStates());
		assert correct;
		Collection<STATE> rsaStates = m_Result.getStates();
		Collection<STATE> rscStates = reachalbeStatesCopy.getStates();
		correct &= ResultChecker.isSubset(rsaStates,rscStates);
		assert correct;
		correct &= ResultChecker.isSubset(rscStates,rsaStates);
		assert correct;
		for (STATE state : reachalbeStatesCopy.getStates()) {
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.internalSuccessors(state)) {
				correct &= m_Reach.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.callSuccessors(state)) {
				correct &= m_Reach.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.returnSuccessors(state)) {
				correct &= m_Reach.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (OutgoingInternalTransition<LETTER, STATE> outTrans : m_Result.internalSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (OutgoingCallTransition<LETTER, STATE> outTrans : m_Result.callSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (OutgoingReturnTransition<LETTER, STATE> outTrans : m_Result.returnSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			Set<STATE> rCSdownStates = reachalbeStatesCopy.getDownStates(state);
			Set<STATE> rCAdownStates = m_Reach.getWithOutDeadEnds().getDownStates(state);
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