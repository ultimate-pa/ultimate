/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


/**
 * Represents complement of deterministic and total nwa.
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class BuchiClosureNwa<LETTER, STATE> implements INestedWordAutomatonOldApi<LETTER, STATE>, IDoubleDeckerAutomaton<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomatonOldApi<LETTER, STATE> mOperand;
	private final Set<STATE> mAcceptingStates;



	
	public BuchiClosureNwa(AutomataLibraryServices services,
			INestedWordAutomaton<LETTER, STATE> operand) {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mOperand = (INestedWordAutomatonOldApi<LETTER, STATE>) operand;
		mAcceptingStates = computeSetOfAcceptingStates();
	}
	
	
	/**
	 * maximize set of accepting states
	 * @return 
	 */
	public Set<STATE> computeSetOfAcceptingStates() {
		Set<STATE> newFinalStates = new HashSet<STATE>();
		mLogger.info("Accepting states before buchiClosure: " + mOperand.getFinalStates().size());
		LinkedHashSet<STATE> worklist = new LinkedHashSet<STATE>();
		newFinalStates.addAll(mOperand.getFinalStates());
		for (STATE fin : mOperand.getFinalStates()) {
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
		mLogger.info("Accepting states after buchiClosure: " + newFinalStates.size());
		return newFinalStates;
	}
	
	/**
	 * Add all predecessors of state that are not in the set newFinalStates 
	 * to worklist.
	 */
	private void addAllNonFinalPredecessors(STATE state, Set<STATE> worklist, Set<STATE> newFinalStates) {
		for (IncomingInternalTransition<LETTER, STATE> inTrans : mOperand.internalPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (IncomingCallTransition<LETTER, STATE> inTrans : mOperand.callPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getPred())) {
				worklist.add(inTrans.getPred());
			}
		}
		for (IncomingReturnTransition<LETTER, STATE> inTrans : mOperand.returnPredecessors(state)) {
			if (!newFinalStates.contains(inTrans.getLinPred())) {
				worklist.add(inTrans.getLinPred());
			}
		}
	}
	
	
	/**
	 * Return true iff all successors of state state is the set newFinalStates.
	 */
	private boolean allSuccessorsAccepting(STATE state, Set<STATE> newFinalStates) {
		for (LETTER symbol : mOperand.lettersInternal(state)) {
			for (STATE succ : mOperand.succInternal(state, symbol)) {
				if (!newFinalStates.contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : mOperand.lettersCall(state)) {
			for (STATE succ : mOperand.succCall(state, symbol)) {
				if (!newFinalStates.contains(succ)) {
					return false;
				}
			}
		}
		for (LETTER symbol : mOperand.lettersReturn(state)) {
			for (STATE hier : mOperand.hierPred(state, symbol)) {
				for (STATE succ : mOperand.succReturn(state, hier, symbol)) {
					if (!newFinalStates.contains(succ)) {
						return false;
					}
				}
			}
		}
		return true;
	}
	
	
	@Override
	public Set<STATE> getInitialStates() {
		return mOperand.getInitialStates();
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return mOperand.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return mOperand.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return mOperand.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return mOperand.getStateFactory();
	}
	
	@Override
	public boolean isInitial(STATE state) {
		return mOperand.isInitial(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return mAcceptingStates.contains(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return mOperand.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		return mOperand.lettersInternal(state);
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		return mOperand.lettersCall(state);
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		return mOperand.lettersReturn(state);
	}


	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state, LETTER letter) {
		return mOperand.internalSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			STATE state) {
		return mOperand.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state, LETTER letter) {
		return mOperand.callSuccessors(state, letter);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			STATE state) {
		return mOperand.callSuccessors(state);
	}



	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(
			STATE state, STATE hier, LETTER letter) {
		return mOperand.returnSucccessors(state, hier, letter);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			STATE state, STATE hier) {
		return mOperand.returnSuccessorsGivenHier(state, hier);
	}

	@Override
	public int size() {
		return mOperand.size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return mOperand.sizeInformation();
	}


	public Set<STATE> getStates() {
		return mOperand.getStates();
	}


	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		return mOperand.hierPred(state, letter);
	}


	public Collection<STATE> getFinalStates() {
		return mAcceptingStates;
	}


	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			LETTER letter, STATE hier) {
		return mOperand.returnSummarySuccessor(letter, hier);
	}


	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			STATE hier) {
		return mOperand.returnSummarySuccessor(hier);
	}


	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			STATE succ) {
		return mOperand.internalPredecessors(succ);
	}


	public Set<LETTER> lettersInternalIncoming(STATE state) {
		return mOperand.lettersInternalIncoming(state);
	}


	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			LETTER letter, STATE succ) {
		return mOperand.internalPredecessors(letter, succ);
	}


	public Set<LETTER> lettersCallIncoming(STATE state) {
		return mOperand.lettersCallIncoming(state);
	}


	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			LETTER letter, STATE succ) {
		return mOperand.callPredecessors(letter, succ);
	}


	public Set<LETTER> lettersReturnIncoming(STATE state) {
		return mOperand.lettersReturnIncoming(state);
	}


	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			STATE succ) {
		return mOperand.callPredecessors(succ);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE hier, LETTER letter, STATE succ) {
		return mOperand.returnPredecessors(hier, letter, succ);
	}


	public Set<LETTER> lettersReturnSummary(STATE state) {
		return mOperand.lettersReturnSummary(state);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			LETTER letter, STATE succ) {
		return mOperand.returnPredecessors(letter, succ);
	}


	public Iterable<STATE> succInternal(STATE state, LETTER letter) {
		return mOperand.succInternal(state, letter);
	}


	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			STATE succ) {
		return mOperand.returnPredecessors(succ);
	}


	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state, LETTER letter) {
		return mOperand.returnSuccessors(state, letter);
	}


	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		return mOperand.succCall(state, letter);
	}


	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			STATE state) {
		return mOperand.returnSuccessors(state);
	}


	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		return mOperand.succReturn(state, hier, letter);
	}


	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return mOperand.predInternal(state, letter);
	}


	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		return mOperand.predCall(state, letter);
	}


	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}


	public boolean isDeterministic() {
		return mOperand.isDeterministic();
	}


	public boolean isTotal() {
		return mOperand.isTotal();
	}


	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).isDoubleDecker(up, down);
	}


	@Override
	public Set<STATE> getDownStates(STATE up) {
		return ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).getDownStates(up);
	}



}
