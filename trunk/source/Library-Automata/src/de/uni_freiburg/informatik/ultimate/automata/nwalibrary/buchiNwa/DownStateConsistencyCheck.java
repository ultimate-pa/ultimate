/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;


/**
 * Check if down states of an automaton are stored consistent.
 * This operation is only useful for debugging.
 * @author heizmann@informatik.uni-freiburg.de
 */
public class DownStateConsistencyCheck<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final IDoubleDeckerAutomaton<LETTER, STATE> m_Operand;
	private final boolean m_Result;
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	
	public DownStateConsistencyCheck(IUltimateServiceProvider services, 
			IDoubleDeckerAutomaton<LETTER, STATE> nwa) throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = nwa;
		m_Result = consistentForAll();
	}
	
	
	@Override
	public String operationName() {
		return "DownStateConsistencyCheck";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Operand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				m_Result;
	}

	@Override
	public Boolean getResult() {
		return m_Result;
	}
	
	public boolean consistentForAll() throws OperationCanceledException {
		boolean result = true;
		result &= consistentForInitials();
		for (STATE state : m_Operand.getStates()) {
			if (!m_Services.getProgressMonitorService().continueProcessing()) {
				throw new OperationCanceledException(this.getClass());
			}
			result &= consistentForState(state);
		}
		return result;
	}
	
	private boolean consistentForInitials() {
		boolean result = true;
		for (STATE state : m_Operand.getInitialStates()) {
			Set<STATE> downStates = m_Operand.getDownStates(state);
			result &= downStates.contains(m_Operand.getEmptyStackState());
		}
		assert result : "down states inconsistent";
		return result;
	}

	private boolean consistentForState(STATE state) {
		boolean result = true;
		Set<STATE> downStates = m_Operand.getDownStates(state);
		result &= getIsComparison(state, downStates);
		result &= checkIfDownStatesArePassedToSuccessors(state, downStates);
		result &= checkIfEachDownStateIsJustified(state, downStates);
		assert result : "down states inconsistent";
		return result;
	}
	
	private boolean checkIfEachDownStateIsJustified(STATE state, Set<STATE> downStates) {
		downStates = new HashSet<STATE>(downStates);
		for (IncomingInternalTransition<LETTER, STATE> t : m_Operand.internalPredecessors(state)) {
			Set<STATE> preDown = m_Operand.getDownStates(t.getPred());
			downStates.removeAll(preDown);
		}

		for (IncomingCallTransition<LETTER, STATE> t : m_Operand.callPredecessors(state)) {
			downStates.remove(t.getPred());
		}

		for (IncomingReturnTransition<LETTER, STATE> t : m_Operand.returnPredecessors(state)) {
			Set<STATE> predDownStates = m_Operand.getDownStates(t.getLinPred());
			if (predDownStates.contains(t.getHierPred())) {
				Set<STATE> hierDownStates = m_Operand.getDownStates(t.getHierPred());
				downStates.removeAll(hierDownStates);
			} else {
				throw new AssertionError("unreachable return");
			}
		}
		if (m_Operand.isInitial(state)) {
			downStates.remove(m_Operand.getEmptyStackState());
		}
		if (!downStates.isEmpty()) {
			m_Logger.warn("State " + state + " has unjustified down states " + downStates );
		}
		return downStates.isEmpty();
	}

	private boolean checkIfDownStatesArePassedToSuccessors(STATE state,
			Set<STATE> downStates) {
		boolean result = true;
		for (OutgoingInternalTransition<LETTER, STATE> t : m_Operand.internalSuccessors(state)) {
			Set<STATE> succDownStates = m_Operand.getDownStates(t.getSucc());
			result &= succDownStates.containsAll(downStates);
			assert result : "down states inconsistent";
		}
		for (OutgoingCallTransition<LETTER, STATE> t : m_Operand.callSuccessors(state)) {
			Set<STATE> succDownStates = m_Operand.getDownStates(t.getSucc());
			result &= succDownStates.contains(state);
			assert result : "down states inconsistent";
		}
		for (OutgoingReturnTransition<LETTER, STATE> t : m_Operand.returnSuccessors(state)) {
			Set<STATE> succDownStates = m_Operand.getDownStates(t.getSucc());
			Set<STATE> hierDownStates = m_Operand.getDownStates(t.getHierPred());
			if (downStates.contains(t.getHierPred())) {
				result &= succDownStates.containsAll(hierDownStates);
				assert result : "down states inconsistent";
			} else {
				// nothing to check, we cannot take this transition
			}
		}
		for (SummaryReturnTransition<LETTER, STATE> t : m_Operand.returnSummarySuccessor(state)) {
			Set<STATE> succDownStates = m_Operand.getDownStates(t.getSucc());
			result &= succDownStates.containsAll(downStates);
			assert result : "down states inconsistent";
		}
		return result;
	}

	/**
	 * Check if {@link IDoubleDeckerAutomaton#getDownStates(Object)} and 
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)} are
	 * consistent.
	 */
	private boolean getIsComparison(STATE state, Set<STATE> downStates) {
		return getIsComparison1(state, downStates) 
				&& getIsComparison2(state, downStates);
	}

	
	/**
	 * Check if doubleDeckers claimed by 
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)}
	 * are a superset of the doubleDeckers claimed by
	 * {@link IDoubleDeckerAutomaton#getDownStates(Object)}
	 */
	private boolean getIsComparison1(STATE state, Set<STATE> downStates) {
		boolean result = true;
		for (STATE down : downStates) {
			result &= m_Operand.isDoubleDecker(state, down);
		}
		return result;
	}
	
	/**
	 * Check if doubleDeckers claimed by 
	 * {@link IDoubleDeckerAutomaton#getDownStates(Object)}
	 * are a superset of the doubleDeckers claimed by
	 * {@link IDoubleDeckerAutomaton#isDoubleDecker(Object, Object)}
	 * This check is expensive, because we have to iterate over all states.
	 * 
	 */
	private boolean getIsComparison2(STATE state, Set<STATE> downStates) {
		boolean result = true;
		for (STATE down : m_Operand.getStates()) {
			if (m_Operand.isDoubleDecker(state, down)) {
				result &= downStates.contains(down);
			}
		}
		return result;
	}



	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		// I don't know a useful check
		return true;
	}

}
