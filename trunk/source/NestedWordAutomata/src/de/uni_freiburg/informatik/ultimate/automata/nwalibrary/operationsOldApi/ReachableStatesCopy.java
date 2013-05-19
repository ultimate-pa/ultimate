package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;

public class ReachableStatesCopy<LETTER,STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation {
	
	private final Map<STATE,STATE> m_old2new = new HashMap<STATE,STATE>();
	private final Map<STATE,STATE> m_new2old = new HashMap<STATE,STATE>();

	private final INestedWordAutomatonOldApi<LETTER,STATE> m_Input;
	private final boolean m_Complement;

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
	public ReachableStatesCopy(INestedWordAutomatonOldApi<LETTER,STATE> nwa,
			boolean totalize, boolean complement,
			boolean removeDeadEnds, boolean removeNonLiveStates)
			throws OperationCanceledException {
		if (complement && !totalize) {
			throw new IllegalArgumentException("complement requires totalize");
		}
		m_Complement = complement;
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_TraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				nwa.getInternalAlphabet(), nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(), nwa.getStateFactory());
		super.m_RemoveDeadEnds = removeDeadEnds;
		super.m_RemoveNonLiveStates = removeNonLiveStates;
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.m_TraversedNwa).setUp2Down(getUp2DownMapping());
		if (totalize || m_Input.getInitialStates().isEmpty()) {
			makeAutomatonTotal();
		}
		s_Logger.info(exitMessage());
	}
	
	
	public ReachableStatesCopy(INestedWordAutomatonOldApi<LETTER,STATE> nwa)
			throws OperationCanceledException {
		m_Input = nwa;
		s_Logger.info(startMessage());
		m_TraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				nwa.getInternalAlphabet(), nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(), nwa.getStateFactory());
		super.m_RemoveDeadEnds = false;
		super.m_RemoveNonLiveStates = false;
		m_Complement = false;
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.m_TraversedNwa).setUp2Down(getUp2DownMapping());
		s_Logger.info(exitMessage());
	}
	
	private void makeAutomatonTotal() {
		STATE sinkState = m_TraversedNwa.getStateFactory().createSinkStateContent();
		boolean isInitial = false; //m_Input.getInitial().isEmpty();
		boolean isFinal = m_Complement;
		((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(isInitial, isFinal, sinkState);
		
		for (STATE state : m_TraversedNwa.getStates()) {
			for (LETTER letter : m_TraversedNwa.getInternalAlphabet()) {				
				if (!m_TraversedNwa.succInternal(state,letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(state, letter, sinkState);
				}
			}
			for (LETTER letter : m_TraversedNwa.getCallAlphabet()) {				
				if (!m_TraversedNwa.succCall(state,letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(state, letter, sinkState);
				}
			}
			for (LETTER symbol : m_TraversedNwa.getReturnAlphabet()) {
				for (STATE hier : m_TraversedNwa.getStates()) {
					if (!m_TraversedNwa.succReturn(state,hier,symbol).iterator().hasNext()) {
						((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(state, hier, symbol, sinkState);
					}
				}
			}
		}
	}

	@Override
	public String operationName() {
		return "reachableStatesCopy";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ m_Input.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ m_TraversedNwa.sizeInformation();
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		Collection<STATE> newInitialStates = new ArrayList<STATE>(m_Input.getInitialStates().size());
		for (STATE oldUpState : m_Input.getInitialStates()) {
			STATE newState = constructOrGetResState(oldUpState, true);
			newInitialStates.add(newState);
		}
		return newInitialStates;
	}

	private STATE constructOrGetResState(STATE oldUp, boolean isInitial) {
		if (m_old2new.containsKey(oldUp)) {
			return m_old2new.get(oldUp);
		}
		STATE newState = m_old2new.get(oldUp);
		if (newState == null) {
			newState = oldUp;
			boolean isAccepting = m_Input.isFinal(oldUp) ^ m_Complement;
			((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(isInitial, isAccepting, newState);
			m_old2new.put(oldUp, newState);
			m_new2old.put(newState, oldUp);
		}
		return newState;

	}

	@Override
	protected Collection<STATE> buildInternalSuccessors(DoubleDecker<STATE> doubleDecker) {
		ArrayList<STATE> succs = new ArrayList<STATE>();
		STATE newUpState = doubleDecker.getUp();
		STATE oldUpState = m_new2old.get(newUpState);
		for (LETTER symbol : m_Input.lettersInternal(oldUpState)) {
			for (STATE oldSucc : m_Input.succInternal(oldUpState, symbol)) {
				STATE newSucc = constructOrGetResState(oldSucc, false);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	protected Collection<STATE> buildReturnSuccessors(DoubleDecker<STATE> doubleDecker) {
		ArrayList<STATE> succs = new ArrayList<STATE>();
		STATE newDownState = doubleDecker.getDown();
		if (newDownState == m_TraversedNwa.getEmptyStackState()) {
			return succs;
		}
		STATE newUpState = doubleDecker.getUp();
		STATE oldUpState = m_new2old.get(newUpState);
		STATE oldDownState = m_new2old.get(newDownState);

		for (LETTER symbol : m_Input.lettersReturn(oldUpState)) {
			for (STATE oldSucc : m_Input.succReturn(oldUpState, oldDownState, symbol)) {
				STATE newSucc = constructOrGetResState(oldSucc, false);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(newUpState, newDownState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	protected Collection<STATE> buildCallSuccessors(DoubleDecker<STATE> doubleDecker) {
		ArrayList<STATE> succs = new ArrayList<STATE>();
		STATE newUpState = doubleDecker.getUp();
		STATE oldUpState = m_new2old.get(newUpState);
		for (LETTER symbol : m_Input.lettersCall(oldUpState)) {
			for (STATE oldSucc : m_Input.succCall(oldUpState, symbol)) {
				STATE newSucc = constructOrGetResState(oldSucc, false);
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}
	
	
	public final INestedWordAutomatonOldApi<LETTER,STATE> getResult() throws OperationCanceledException {
		if (!m_RemoveNonLiveStates) {
			if (!m_Complement) {
				assert (ResultChecker.minimize(m_Input, m_TraversedNwa));
			} else {
				assert (ResultChecker.complement(m_Input, m_TraversedNwa));
			}
		}
		return m_TraversedNwa;
	}


}