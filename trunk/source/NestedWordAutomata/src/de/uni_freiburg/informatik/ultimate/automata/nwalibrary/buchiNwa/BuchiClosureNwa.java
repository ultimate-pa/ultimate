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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.Activator;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.api.UltimateServices;


/**
 * Represents complement of deterministic and total nwa.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class BuchiClosureNwa<LETTER, STATE> implements INestedWordAutomatonOldApi<LETTER, STATE>, IDoubleDeckerAutomaton<LETTER, STATE> {
	private static Logger s_Logger = 
			UltimateServices.getInstance().getLogger(Activator.PLUGIN_ID);
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	private final Set<STATE> m_AcceptingStates;

	
	public BuchiClosureNwa(INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		m_Operand = operand;
		m_AcceptingStates = computeSetOfAcceptingStates();
	}
	
	
	/**
	 * maximize set of accepting states
	 * @return 
	 */
	public Set<STATE> computeSetOfAcceptingStates() {
		Set<STATE> newFinalStates = new HashSet<STATE>();
		s_Logger.info("Accepting states before buchiClosure: " + m_Operand.getFinalStates().size());
		LinkedHashSet<STATE> worklist = new LinkedHashSet<STATE>();
		newFinalStates.addAll(m_Operand.getFinalStates());
		for (STATE fin : m_Operand.getFinalStates()) {
			addAllNonFinalPredecessors(fin, worklist, newFinalStates);
		}
		while (!worklist.isEmpty()) {
			STATE state = worklist.iterator().next();
			worklist.remove(state);
			assert !newFinalStates.contains(state);
			if (allSuccessorsAccepting(state, newFinalStates)) {
				newFinalStates.add(state);
				addAllNonFinalPredecessors(state, worklist, newFinalStates);
			}
		}
		s_Logger.info("Accepting states after buchiClosure: " + newFinalStates.size());
		return newFinalStates;
	}
	
	/**
	 * Add all predecessors of state that are not in the set newFinalStates 
	 * to worklist.
	 */
	private void addAllNonFinalPredecessors(STATE state, Set<STATE> worklist, Set<STATE> newFinalStates) {
		for (IncomingInternalTransition<LETTER, STATE> inTrans : m_Operand.internalPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (IncomingCallTransition<LETTER, STATE> inTrans : m_Operand.callPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (IncomingReturnTransition<LETTER, STATE> inTrans : m_Operand.returnPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getLinPred())) {
				worklist.add(inTrans.getLinPred());
			}
		}
	}
	
	
	/**
	 * Return true iff all successors of state state is the set newFinalStates.
	 */
	private boolean allSuccessorsAccepting(STATE state, Set<STATE> newFinalStates) {
		for (LETTER symbol : m_Operand.lettersInternal(state)) {
			for (STATE succ : m_Operand.succInternal(state, symbol)) {
				if (!newFinalStates.contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : m_Operand.lettersCall(state)) {
			for (STATE succ : m_Operand.succCall(state, symbol)) {
				if (!newFinalStates.contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : m_Operand.lettersReturn(state)) {
			for (STATE hier : m_Operand.hierPred(state, symbol)) {
				for (STATE succ : m_Operand.succReturn(state, hier, symbol)) {
					if (!newFinalStates.contains(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	@Override
	public Collection<STATE> getInitialStates() {
		return m_Operand.getInitialStates();
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Operand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Operand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Operand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_Operand.getStateFactory();
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return m_Operand.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_AcceptingStates.contains(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Operand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return m_Operand.lettersInternal(state);
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return m_Operand.lettersCall(state);
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return m_Operand.lettersReturn(state);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		return m_Operand.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		return m_Operand.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		return m_Operand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		return m_Operand.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		return m_Operand.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		return m_Operand.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		return m_Operand.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return m_Operand.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return m_Operand.sizeInformation();
	}


	public Collection<STATE> getStates() {
		return m_Operand.getStates();
	}


	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return m_Operand.hierPred(state, letter);
	}


	public Collection<STATE> getFinalStates() {
		return m_AcceptingStates;
	}


	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			LETTER letter, STATE hier) {
		return m_Operand.returnSummarySuccessor(letter, hier);
	}


	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			STATE hier) {
		return m_Operand.returnSummarySuccessor(hier);
	}


	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			STATE succ) {
		return m_Operand.internalPredecessors(succ);
	}


	public Set<LETTER> lettersInternalIncoming(STATE state) {
		return m_Operand.lettersInternalIncoming(state);
	}


	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter, STATE succ) {
		return m_Operand.internalPredecessors(letter, succ);
	}


	public Set<LETTER> lettersCallIncoming(STATE state) {
		return m_Operand.lettersCallIncoming(state);
	}


	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter, STATE succ) {
		return m_Operand.callPredecessors(letter, succ);
	}


	public Set<LETTER> lettersReturnIncoming(STATE state) {
		return m_Operand.lettersReturnIncoming(state);
	}


	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			STATE succ) {
		return m_Operand.callPredecessors(succ);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter, STATE succ) {
		return m_Operand.returnPredecessors(hier, letter, succ);
	}


	public Set<LETTER> lettersReturnSummary(STATE state) {
		return m_Operand.lettersReturnSummary(state);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter, STATE succ) {
		return m_Operand.returnPredecessors(letter, succ);
	}


	public Iterable<STATE> succInternal(STATE state, LETTER letter) {
		return m_Operand.succInternal(state, letter);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		return m_Operand.returnPredecessors(succ);
	}


	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, LETTER letter) {
		return m_Operand.returnSuccessors(state, letter);
	}


	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		return m_Operand.succCall(state, letter);
	}


	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state) {
		return m_Operand.returnSuccessors(state);
	}


	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return m_Operand.succReturn(state, hier, letter);
	}


	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return m_Operand.predInternal(state, letter);
	}


	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		return m_Operand.predCall(state, letter);
	}


	public Iterable<STATE> predReturnLin(STATE state, LETTER letter, STATE hier) {
		return m_Operand.predReturnLin(state, letter, hier);
	}


	public Iterable<STATE> predReturnHier(STATE state, LETTER letter) {
		return m_Operand.predReturnHier(state, letter);
	}


	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}


	public boolean isDeterministic() {
		return m_Operand.isDeterministic();
	}


	public boolean isTotal() {
		return m_Operand.isTotal();
	}


	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) m_Operand).isDoubleDecker(up, down);
	}


	@Override
	public Set<STATE> getDownStates(STATE up) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) m_Operand).getDownStates(up);
	}



}
