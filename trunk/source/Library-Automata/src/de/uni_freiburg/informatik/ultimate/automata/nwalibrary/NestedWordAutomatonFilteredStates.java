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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AtsDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.DownStateConsistencyCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.StateBasedTransitionFilterPredicateProvider;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.services.IUltimateServiceProvider;
import de.uni_freiburg.informatik.ultimate.util.FilteredIterable;
import de.uni_freiburg.informatik.ultimate.util.IPredicate;

public class NestedWordAutomatonFilteredStates<LETTER, STATE> implements
		INestedWordAutomatonOldApi<LETTER, STATE>, INestedWordAutomaton<LETTER, STATE>, IDoubleDeckerAutomaton<LETTER, STATE> {
	private final IUltimateServiceProvider m_Services;
	private final Logger m_Logger;
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Nwa;
	private final Set<STATE> m_RemainingStates;
	private final Set<STATE> m_newInitials;
	private final Set<STATE> m_newFinals;
	private final NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation m_AncestorComputation;
	private final StateBasedTransitionFilterPredicateProvider<LETTER, STATE> m_TransitionFilter;
	
	NestedWordAutomatonFilteredStates(IUltimateServiceProvider services,
			INestedWordAutomatonOldApi<LETTER, STATE> automaton, 
			Set<STATE> remainingStates, Set<STATE> newInitials, Set<STATE> newFinals) 
					throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Nwa = automaton;
		m_RemainingStates = remainingStates;
		m_newInitials = newInitials;
		m_newFinals = newFinals;
		m_AncestorComputation = null;
		m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(m_RemainingStates);
		assert (new DownStateConsistencyCheck<LETTER, STATE>(m_Services, this)).getResult() : "down states inconsistent";
	}
	
	public NestedWordAutomatonFilteredStates(
			IUltimateServiceProvider services,
			NestedWordAutomatonReachableStates<LETTER, STATE> automaton, 
			NestedWordAutomatonReachableStates<LETTER, STATE>.AncestorComputation ancestorComputation) 
					throws OperationCanceledException {
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Nwa = automaton;
		m_RemainingStates = ancestorComputation.getStates();
		m_newInitials = ancestorComputation.getInitials();
		m_newFinals = ancestorComputation.getFinals();
		m_AncestorComputation = ancestorComputation;
		m_TransitionFilter = new StateBasedTransitionFilterPredicateProvider<>(m_RemainingStates);
		assert (new DownStateConsistencyCheck<LETTER, STATE>(m_Services, this)).getResult() : "down states inconsistent";
	}
	
	public Set<STATE> getDownStates(STATE up) {
		if (m_AncestorComputation != null) {
			return m_AncestorComputation.getDownStates(up);
		}
		throw new UnsupportedOperationException();
	}

	@Override
	public int size() {
		return getStates().size();
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return m_Nwa.getAlphabet();
	}

	@Override
	public String sizeInformation() {
		return m_RemainingStates.size() + " states.";
	}

	@Override
	public Set<LETTER> getInternalAlphabet() {
		return m_Nwa.getInternalAlphabet();
	}

	@Override
	public Set<LETTER> getCallAlphabet() {
		return m_Nwa.getCallAlphabet();
	}

	@Override
	public Set<LETTER> getReturnAlphabet() {
		return m_Nwa.getReturnAlphabet();
	}

	@Override
	public StateFactory<STATE> getStateFactory() {
		return m_Nwa.getStateFactory();
	}

	@Override
	public Set<STATE> getStates() {
		return m_RemainingStates;
	}

	@Override
	public Set<STATE> getInitialStates() {
		return m_newInitials;
	}

	@Override
	public Collection<STATE> getFinalStates() {
		return m_newFinals;
	}

	@Override
	public boolean isInitial(STATE state) {
		return m_newInitials.contains(state);
	}

	@Override
	public boolean isFinal(STATE state) {
		return m_newFinals.contains(state);
	}

	@Override
	public STATE getEmptyStackState() {
		return m_Nwa.getEmptyStackState();
	}

	@Override
	public Set<LETTER> lettersInternal(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingInternalTransition<LETTER, STATE> outTrans : internalSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersCall(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingCallTransition<LETTER, STATE> outTrans : callSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturn(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersInternalIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingInternalTransition<LETTER, STATE> outTrans : internalPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersCallIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingCallTransition<LETTER, STATE> outTrans : callPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturnIncoming(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (IncomingReturnTransition<LETTER, STATE> outTrans : returnPredecessors(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Set<LETTER> lettersReturnSummary(STATE state) {
		Set<LETTER> letters = new HashSet<LETTER>();
		for (SummaryReturnTransition<LETTER, STATE> outTrans : returnSummarySuccessor(state)) {
			letters.add(outTrans.getLetter());
		}
		return letters;
	}

	@Override
	public Iterable<STATE> succInternal(final STATE state, final LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.succInternal(state, letter), new IPredicate.SetBasedPredicate<>(m_RemainingStates));
	}

	@Override
	public Iterable<STATE> succCall(STATE state, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for ( OutgoingCallTransition<LETTER, STATE> outTrans  : callSuccessors(state, letter)) {
			result.add(outTrans.getSucc());
		}
		return result;
	}

	@Override
	public Iterable<STATE> hierPred(STATE state, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSuccessors(state, letter)) {
			if (m_RemainingStates.contains(outTrans.getHierPred()) && m_RemainingStates.contains(outTrans.getSucc())) {
				result.add(outTrans.getHierPred());
			}
		}
		return result;
	}

	@Override
	public Iterable<STATE> succReturn(STATE state, STATE hier, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for (OutgoingReturnTransition<LETTER, STATE> outTrans : returnSucccessors(state, hier, letter)) {
			if (m_RemainingStates.contains(outTrans.getHierPred()) && m_RemainingStates.contains(outTrans.getSucc())) {
				result.add(outTrans.getSucc());
			}
		}
		return result;
	}

	@Override
	public Iterable<STATE> predInternal(STATE state, LETTER letter) {
		return new FilteredIterable<STATE>(m_Nwa.predInternal(state, letter), new IPredicate.SetBasedPredicate<>(m_RemainingStates));
	}

	@Override
	public Iterable<STATE> predCall(STATE state, LETTER letter) {
		Set<STATE> result = new HashSet<STATE>();
		for (IncomingCallTransition<LETTER, STATE> inTrans  : callPredecessors(letter, state)) {
			result.add(inTrans.getPred());
		}
		return result;
	}

	@Override
	public boolean finalIsTrap() {
		throw new UnsupportedOperationException();
	}

	@Override
	public boolean isDeterministic() {
		return false;
	}

	@Override
	public boolean isTotal() {
		throw new UnsupportedOperationException();
	}



	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(LETTER letter, STATE succ) {
		IPredicate<IncomingInternalTransition<LETTER, STATE>> predicate = m_TransitionFilter.getInternalPredecessorsPredicate();
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(m_Nwa.internalPredecessors(letter,succ), predicate);
	}

	@Override
	public Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(STATE succ) {
		IPredicate<IncomingInternalTransition<LETTER, STATE>> predicate = m_TransitionFilter.getInternalPredecessorsPredicate();
		return new FilteredIterable<IncomingInternalTransition<LETTER, STATE>>(m_Nwa.internalPredecessors(succ), predicate);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(LETTER letter, final STATE succ) {
		IPredicate<IncomingCallTransition<LETTER, STATE>> predicate = new IPredicate<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingCallTransition<LETTER, STATE> trans) {
				// filter out also transitions that are not contained any more 
				// because (succ, trans.getPred()) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getPred()) && isDoubleDecker(succ, trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(letter,succ), predicate);
	}

	@Override
	public Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ) {
		IPredicate<IncomingCallTransition<LETTER, STATE>> predicate = new IPredicate<IncomingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(IncomingCallTransition<LETTER, STATE> trans) {
				// filter out also transitions that are not contained any more 
				// because (succ, trans.getPred()) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getPred()) && isDoubleDecker(succ, trans.getPred());
			}
		};
		return new FilteredIterable<IncomingCallTransition<LETTER, STATE>>(m_Nwa.callPredecessors(succ), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state, LETTER letter) {
		IPredicate<OutgoingInternalTransition<LETTER, STATE>> predicate = m_TransitionFilter.getInternalSuccessorPredicate();
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(STATE state) {
		IPredicate<OutgoingInternalTransition<LETTER, STATE>> predicate = m_TransitionFilter.getInternalSuccessorPredicate();
		return new FilteredIterable<OutgoingInternalTransition<LETTER, STATE>>(m_Nwa.internalSuccessors(state), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, LETTER letter) {
		IPredicate<OutgoingCallTransition<LETTER, STATE>> predicate = new IPredicate<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingCallTransition<LETTER, STATE> trans) {
				// filter out also transitions that are not contained any more 
				// because (trans.getSucc(), state) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getSucc()) && isDoubleDecker(trans.getSucc(), state);
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state,letter), predicate);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		IPredicate<OutgoingCallTransition<LETTER, STATE>> predicate = new IPredicate<OutgoingCallTransition<LETTER,STATE>>() {
			@Override
			public boolean evaluate(OutgoingCallTransition<LETTER, STATE> trans) {
				// filter out also transitions that are not contained any more 
				// because (trans.getSucc(), state) is not a DoubleDecker of the
				// resulting automaton
				return m_RemainingStates.contains(trans.getSucc()) && isDoubleDecker(trans.getSucc(), state);
			}
		};
		return new FilteredIterable<OutgoingCallTransition<LETTER, STATE>>(m_Nwa.callSuccessors(state), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE hier, LETTER letter, STATE succ) {
		IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(hier, letter, succ), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(LETTER letter, STATE succ) {
		IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(letter, succ), predicate);
	}

	@Override
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(STATE succ) {
		IPredicate<IncomingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnPredecessorPredicate();
		return new FilteredIterable<IncomingReturnTransition<LETTER, STATE>>(m_Nwa.returnPredecessors(succ), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSucccessors(STATE state, STATE hier, LETTER letter) {
		IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSucccessors(state,hier,letter), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state, LETTER letter) {
		IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessors(state, letter), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(STATE state) {
		IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessors(state), predicate);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(STATE state, STATE hier) {
		IPredicate<OutgoingReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSuccessorPredicate();
		return new FilteredIterable<OutgoingReturnTransition<LETTER, STATE>>(m_Nwa.returnSuccessorsGivenHier(state,hier), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(LETTER letter, STATE hier) {
		IPredicate<SummaryReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSummaryPredicate();
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(m_Nwa.returnSummarySuccessor(letter, hier), predicate);
	}
	
	@Override
	public Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(STATE hier) {
		IPredicate<SummaryReturnTransition<LETTER, STATE>> predicate = m_TransitionFilter.getReturnSummaryPredicate();
		return new FilteredIterable<SummaryReturnTransition<LETTER, STATE>>(m_Nwa.returnSummarySuccessor(hier), predicate);
	}
	
	@Override
	public String toString() {
		return (new AtsDefinitionPrinter<String,String>(m_Services, "nwa", this)).getDefinitionAsString();
	}
	
	
	@Override
	public boolean isDoubleDecker(STATE up, STATE down) {
		return m_AncestorComputation.isDownState(up, down);
	}
	
	
}
