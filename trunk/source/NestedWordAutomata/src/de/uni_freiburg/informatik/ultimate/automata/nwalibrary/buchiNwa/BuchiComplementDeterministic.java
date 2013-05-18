package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * BNWA complementation that works only for deterministic Buchi automata
 */

//FIXME: return in final part may take nonfinal state from stack

public class BuchiComplementDeterministic<LETTER,STATE> extends DoubleDeckerVisitor<LETTER,STATE>
											   implements IOperation {
	
	private static Logger s_Logger = 
		UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_Operand;
	private final INestedWordAutomatonOldApi<LETTER,STATE> m_TotalizedOperand;
	private final StateFactory<STATE> m_ContentFactory;
	
	private final HashMap<STATE,STATE> m_New2Old = new HashMap<STATE,STATE>();
	
	private final HashMap<STATE,STATE> m_Old2Final = new HashMap<STATE,STATE>();
	private final HashMap<STATE,STATE> m_Old2NonFinal = new HashMap<STATE,STATE>();


	
	
	
	
	@Override
	public String operationName() {
		return "buchiComplementDeterministic";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
			m_TraversedNwa.sizeInformation();
	}
	
	public BuchiComplementDeterministic(INestedWordAutomatonOldApi<LETTER,STATE> nwa) throws OperationCanceledException {
		m_Operand = nwa;
		m_ContentFactory = m_Operand.getStateFactory();
		s_Logger.info(startMessage());
		if (m_Operand.isTotal()) {
			m_TotalizedOperand = m_Operand;
		}
		else { 			
			m_TotalizedOperand = new ReachableStatesCopy<LETTER,STATE>(nwa, true, false, false, false).getResult();
		}
		m_TraversedNwa = new NestedWordAutomaton<LETTER,STATE>(
				nwa.getInternalAlphabet(),
				nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(),
				nwa.getStateFactory());
		traverseDoubleDeckerGraph();
		s_Logger.info(exitMessage());
		
	}
	
	
	
	
	
	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws OperationCanceledException {
		assert ResultChecker.buchiComplement(m_Operand, m_TraversedNwa);
		return m_TraversedNwa;
	}

	STATE getOrConstructNewState(STATE oldState, boolean isInitial, boolean isFinal) {
		STATE newState;
		STATE newContent;
		if (isFinal) {
			newState = m_Old2Final.get(oldState);
			newContent = m_ContentFactory.complementBuchiDeterministicFinal(oldState);
		}
		else {
			newState = m_Old2NonFinal.get(oldState);
			newContent = m_ContentFactory.complementBuchiDeterministicNonFinal(oldState);
		}
		if (newState == null) {
			if (isFinal) {
				newState = newContent;
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(isInitial, isFinal, newState);
				m_Old2Final.put(oldState,newState);
			}
			else {
				newState = newContent;
				((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addState(isInitial, isFinal, newState);
				m_Old2NonFinal.put(oldState,newState);
			}
			m_New2Old.put(newState,oldState);
		}
		return newState;
	}

	@Override
	protected Collection<STATE> getInitialStates() {
		Collection<STATE> oldInitialStates = 
											m_TotalizedOperand.getInitialStates();
		assert(oldInitialStates.size() == 1);
		STATE oldInit = null;
		for (STATE state : m_TotalizedOperand.getInitialStates()) {
			oldInit = state;
		}
		STATE newInit = getOrConstructNewState(oldInit, true, false);
		ArrayList<STATE> newInitialStates = new ArrayList<STATE>(1);
		newInitialStates.add(newInit);
		return newInitialStates;
	}

	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> newSuccs = new ArrayList<STATE>();
		STATE newState = doubleDecker.getUp();
		boolean isFinal = m_TraversedNwa.isFinal(newState);
		STATE oldState = m_New2Old.get(newState);
		for (LETTER symbol : m_TotalizedOperand.lettersCall(oldState)) {
			for (STATE succ : m_TotalizedOperand.succCall(oldState, symbol)) {
				if (!isFinal) {
					STATE newSuccNonFinal = getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(newState, symbol, newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if(!m_TotalizedOperand.isFinal(succ)) {
					STATE newSuccFinal = getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addCallTransition(newState, symbol, newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}

	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> newSuccs = new ArrayList<STATE>();
		STATE newState = doubleDecker.getUp();
		boolean isFinal = m_TraversedNwa.isFinal(newState);
		STATE oldState = m_New2Old.get(newState);
		for (LETTER symbol : m_TotalizedOperand.lettersInternal(oldState)) {
			for (STATE succ : m_TotalizedOperand.succInternal(oldState, symbol)) {
				if (!isFinal) {
					STATE newSuccNonFinal = getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(newState, symbol, newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if(!m_TotalizedOperand.isFinal(succ)) {
					STATE newSuccFinal = getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addInternalTransition(newState, symbol, newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}

	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			DoubleDecker<STATE> doubleDecker) {
		Collection<STATE> newSuccs = new ArrayList<STATE>();
		STATE newHier = doubleDecker.getDown();
		if (newHier == m_TraversedNwa.getEmptyStackState()) {
			return newSuccs;
		}
		STATE oldHier = m_New2Old.get(newHier);
		
		STATE newState = doubleDecker.getUp();
		boolean isFinal = m_TraversedNwa.isFinal(newState);
		STATE oldState = m_New2Old.get(newState);
		for (LETTER symbol : m_TotalizedOperand.lettersReturn(oldState)) {
			for (STATE succ : m_TotalizedOperand.succReturn(oldState, oldHier, symbol)) {
				if (!isFinal) {
					STATE newSuccNonFinal = 
									getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(newState, newHier, symbol, newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if(!m_TotalizedOperand.isFinal(succ)) {
					STATE newSuccFinal = 
									getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) m_TraversedNwa).addReturnTransition(newState, newHier, symbol, newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}


}
