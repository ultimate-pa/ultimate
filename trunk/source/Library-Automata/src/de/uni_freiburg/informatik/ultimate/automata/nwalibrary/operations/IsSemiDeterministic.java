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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

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
	private final NestedWordAutomatonReachableStates<LETTER, STATE> m_Nwa;
	
	
	@Override
	public String operationName() {
		return "isSemiDeterministic";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + 
			m_Nwa.sizeInformation();
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
			m_Nwa = (NestedWordAutomatonReachableStates<LETTER, STATE>) input;
		} else {
			m_Nwa = new NestedWordAutomatonReachableStates<LETTER, STATE>(m_Services, input);
		}
		m_Logger.info(startMessage());
		iterate();
		m_Result = m_NondeterministicSuccessorOfAccepting.isEmpty();
		m_Logger.info(exitMessage());
	}
	
	public void iterate() {
		Set<DoubleDecker<STATE>> visited = new HashSet<>();
		ArrayDeque<DoubleDecker<STATE>> worklist = new ArrayDeque<>();
		
		// step one: start with finals,
		//           add all non-call successors
		{
			Set<DoubleDecker<STATE>> finalDoubleDeckers = getFinalDoubleDeckers();
			visited.addAll(finalDoubleDeckers);
			worklist.addAll(finalDoubleDeckers);
		}
		while (!worklist.isEmpty()) {
			DoubleDecker<STATE> dd = worklist.remove();
			if (isNondeterministic(dd, m_Nwa)) {
				m_NondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			Set<DoubleDecker<STATE>> succs = getNonCallSuccessors(dd, m_Nwa);
			for (DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}

		// step two: start with yet visited DoubleDeckers, 
		//           add all non-return successors
		{
			worklist.addAll(visited);
		}
		while (!worklist.isEmpty()) {
			DoubleDecker<STATE> dd = worklist.remove();
			if (isNondeterministic(dd, m_Nwa)) {
				m_NondeterministicSuccessorOfAccepting.add(dd.getUp());
			}
			Set<DoubleDecker<STATE>> succs = getNonReturnSuccessors(dd, m_Nwa);
			for (DoubleDecker<STATE> succ : succs) {
				if (!visited.contains(succ)) {
					worklist.add(succ);
					visited.add(succ);
				}
			}
		}
		
	}
	
	private Set<DoubleDecker<STATE>> getFinalDoubleDeckers() {
		Set<DoubleDecker<STATE>> result = new HashSet<>();
		for (STATE fin : m_Nwa.getFinalStates()) {
			for (STATE down : m_Nwa.getDownStates(fin)) {
				result.add(new DoubleDecker<STATE>(down, fin));
			}
		}
		return result;
	}


	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonCallSuccessors(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		Set<DoubleDecker<STATE>> succs = new HashSet<DoubleDecker<STATE>>();
		for (OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (SummaryReturnTransition<LETTER, STATE> out : nwa.returnSummarySuccessor(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSuccessorsGivenHier(dd.getUp(), dd.getDown())) {
			for (STATE downOfHier : nwa.getDownStates(dd.getDown())) {
				succs.add(new DoubleDecker<STATE>(downOfHier, out.getSucc()));
			}
		}
		return succs;
	}
	
	
	private static <LETTER, STATE> Set<DoubleDecker<STATE>> getNonReturnSuccessors(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> nwa) {
		Set<DoubleDecker<STATE>> succs = new HashSet<DoubleDecker<STATE>>();
		for (OutgoingInternalTransition<LETTER, STATE> out : nwa.internalSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (SummaryReturnTransition<LETTER, STATE> out : nwa.returnSummarySuccessor(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getDown(), out.getSucc()));
		}
		for (OutgoingCallTransition<LETTER, STATE> out : nwa.callSuccessors(dd.getUp())) {
			succs.add(new DoubleDecker<STATE>(dd.getUp(), out.getSucc()));
		}
		return succs;
	}

	

	public static <LETTER, STATE> boolean isNondeterministic(DoubleDecker<STATE> dd, NestedWordAutomatonReachableStates<LETTER, STATE> traversedNwa) {
		boolean isNondeterministicInternal = isNondeterministicInternal(dd.getUp(), traversedNwa);
		boolean isNondeterministicCall = isNondeterministicCall(dd.getUp(), traversedNwa);
		boolean isNondeterministicReturn = isNondeterministicReturnGivenHier(dd.getUp(), dd.getDown(), traversedNwa);
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
	
	public static <LETTER, STATE> boolean isNondeterministicReturnGivenHier(STATE state, STATE hier, INestedWordAutomaton<LETTER, STATE> nwa) {
		for (LETTER letter : nwa.lettersReturn(state)) {
			int numberOfSuccs = 0;
			for (@SuppressWarnings("unused") OutgoingReturnTransition<LETTER, STATE> out : nwa.returnSucccessors(state, hier, letter)) {
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

