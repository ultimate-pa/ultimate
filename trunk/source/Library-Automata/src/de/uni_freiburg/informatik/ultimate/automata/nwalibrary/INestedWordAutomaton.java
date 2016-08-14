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
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.SummaryReturnTransition;

/**
 * Interface for data structures that implement nested word automata.
 * 
 * @see INestedWordAutomatonSimple
 * @author Matthias Heizmann
 *
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public interface INestedWordAutomaton<LETTER, STATE>
		extends INestedWordAutomatonSimple<LETTER, STATE> {

	/**
	 * @return The set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly.
	 */
	Set<STATE> getStates();

	/**
	 * @return The set of initial states. 
	 */
	@Override
	Set<STATE> getInitialStates();
	
	/**
	 * @return The set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly. Use the
	 * {@link isFinal} method to check if a specific state is final. 	
	 */
	Collection<STATE> getFinalStates();

	/**
	 * @param state state
	 * @return All letters a such that state has an incoming internal 
	 * transition labeled with letter a.
	 */
	Set<LETTER> lettersInternalIncoming(STATE state);
	
	/**
	 * @param state state
	 * @return All letters a such that state has an incoming call 
	 * transition labeled with letter a.
	 */	
	Set<LETTER> lettersCallIncoming(STATE state);
	
	/**
	 * @param state state
	 * @return All letters a such that state has an incoming return 
	 * transition labeled with letter a.
	 */		
	Set<LETTER> lettersReturnIncoming(STATE state);
	
	/**
	 * @param state state
	 * @return All letters a such that state occurs as hierarchical predecessor
	 * in a return transition labeled with letter a.
	 */
	Set<LETTER> lettersReturnSummary(STATE state);
	
	/**
	 * @param state state
	 * @param letter letter
	 * @return All states hier such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	Iterable<STATE> hierPred(STATE state, LETTER letter);
	
	/**
	 * @param hier hierarchical state
	 * @param letter letter
	 * @return outgoing summary transitions
	 */
	Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final STATE hier, final LETTER letter);
	
	/**
	 * @param hier hierarchical state
	 * @return outgoing summary transitions
	 */
	Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final STATE hier);
	
	/**
	 * @param succ successor state
	 * @return incoming internal transitions
	 */
	Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ);
	
	/**
	 * @param succ successor state
	 * @param letter letter
	 * @return incoming internal transitions
	 */
	Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ, final LETTER letter);
	
	/**
	 * @param succ successor state
	 * @param letter letter
	 * @return incoming call transitions
	 */
	Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ, final LETTER letter);
	
	/**
	 * @param succ successor state
	 * @return incoming internal transitions
	 */
	Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ);
	
	/**
	 * @param succ successor state
	 * @param hier hierarchical predecessor
	 * @param letter letter
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final STATE hier, final LETTER letter);
	
	/**
	 * @param succ successor state
	 * @param letter letter
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ, final LETTER letter);
	
	/**
	 * @param succ successor state
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ);
	
	/**
	 * @param state state
	 * @param letter letter
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter);
	
	/**
	 * @param state state
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state);
}
