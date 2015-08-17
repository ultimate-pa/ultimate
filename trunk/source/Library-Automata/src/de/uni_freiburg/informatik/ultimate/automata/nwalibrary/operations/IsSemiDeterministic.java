/*
 * Copyright (C) 2009-2014 University of Freiburg
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
 * along with the ULTIMATE Automata Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;

/**
 * Check if an automaton is 
 * <a href="https://en.wikipedia.org/wiki/Semi-deterministic_B%C3%BCchi_automaton">Semi-deterministic</a>.
 * @author Matthias Heizmann
 */
public class IsSemiDeterministic<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	protected final IUltimateServiceProvider m_Services;
	protected final Logger m_Logger;
	
	private final Set<STATE> m_NondeterministicSuccessorOfAccepting = new HashSet<>();

	private boolean m_Result;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_TraversedNwa;
	
	
	@Override
	public String operationName() {
		return "isSemiDeterministic";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_TraversedNwa.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand is " 
					+ (m_Result ? "" : "not") + "semideterministic."
					+ " There are " + m_NondeterministicSuccessorOfAccepting + 
					"nondeterministic non-strict successor of accepting states."; 
	}
	
	
	public IsSemiDeterministic(IUltimateServiceProvider services,
			INestedWordAutomatonSimple<LETTER,STATE> input) throws AutomataLibraryException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		if (input instanceof NestedWordAutomatonReachableStates) {
			m_TraversedNwa = (NestedWordAutomatonReachableStates<LETTER, STATE>) input;
		} else {
			m_TraversedNwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, input);
		}
		m_Logger.info(startMessage());
		iterate();
		m_Result = m_NondeterministicSuccessorOfAccepting.isEmpty();
		m_Logger.info(exitMessage());
	}
	
	public void iterate() {
		Set<STATE> visited = new HashSet<STATE>();
		ArrayDeque<STATE> worklist = new ArrayDeque<>();
		
		{
			visited.addAll(m_TraversedNwa.getFinalStates());
			worklist.addAll(m_TraversedNwa.getFinalStates());
		}
		while (!worklist.isEmpty()) {
			STATE state = worklist.remove();
			if (isNondeterministic(state, m_TraversedNwa)) {
				m_NondeterministicSuccessorOfAccepting.add(state);
			}
			Set<STATE> succs = getSuccessors(state, m_TraversedNwa);
			for (STATE succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}
		
	}
	
	private Set<STATE> getSuccessors(STATE state, NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		Set<STATE> succs = new HashSet<STATE>();
		for (OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(state)) {
			succs.add(out.getSucc());
		}
		for (OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(state)) {
			succs.add(out.getSucc());
		}
		for (OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessors(state)) {
			succs.add(out.getSucc());
		}
		return succs;
	}

	public static <LETTER, STATE> boolean isNondeterministic(STATE state, INestedWordAutomaton<LETTER, STATE> nwa) {
		boolean isNondeterministicInternal = isNondeterministicInternal(state, nwa);
		boolean isNondeterministicCall = isNondeterministicCall(state, nwa);
		boolean isNondeterministicReturn = isNondeterministicReturn(state, nwa);
		return isNondeterministicInternal || isNondeterministicCall || isNondeterministicReturn;
	}
	
	public static <LETTER, STATE> boolean isNondeterministicInternal(STATE state, INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		for (LETTER letter : nwa.lettersInternal(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(state, letter)) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}
	
	
	public static <LETTER, STATE> boolean isNondeterministicCall(STATE state, INestedWordAutomatonSimple<LETTER, STATE> nwa) {
		for (LETTER letter : nwa.lettersCall(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(state, letter)) {
				numberOfSuccs++;
			}
			if (numberOfSuccs > 1) {
				return true;
			}
		}
		return false;
	}
	
	public static <LETTER, STATE> boolean isNondeterministicReturn(STATE state, INestedWordAutomaton<LETTER, STATE> nwa) {
		for (LETTER letter : nwa.lettersReturn(state)) {
			for (STATE hier : nwa.hierPred(state, letter)) {
				int numberOfSuccs = 0;
				for (@SuppressWarnings("unused") OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSucccessors(state, hier, letter)) {
					numberOfSuccs++;
				}
				if (numberOfSuccs > 1) {
					return true;
				}
			}
		}
		return false;
	}
	
	
	@Override
	public Boolean getResult() {
		return m_Result;
	}


	@Override
	public boolean checkResult(StateFactory<STATE> sf) throws AutomataLibraryException {
		boolean correct = true;
		return correct;
	}
	
	
}

