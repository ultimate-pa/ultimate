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
package de.uni_freiburg.informatik.ultimate.automata.nestedword;

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.IncomingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.SummaryReturnTransition;

/**
 * Interface for data structures that implement nested word automata.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 * @see INwaOutgoingLetterAndTransitionProvider
 */
public interface INestedWordAutomaton<LETTER, STATE> extends INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {
	/**
	 * @return The set of states of this automaton. <b>Use with caution!</b> Some implementations (e.g., automaton which
	 *         represents result of a complementation) construct their set of states on the fly.
	 *         <p>
	 *         Using the
	 *         {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider# getInitialStates()
	 *         getInitialStates()} method and the successor methods is preferred.
	 */
	Set<STATE> getStates();

	/**
	 * @return The set of initial states.
	 *         <p>
	 *         For iteration, the
	 *         {@link de.uni_freiburg.informatik.ultimate.automata.nestedword .INwaOutgoingLetterAndTransitionProvider#InitialStates()
	 *         getInitialStates()} method is preferred.<br>
	 *         To perform a check for an initial state, the
	 *         {@link de.uni_freiburg.informatik.ultimate.automata .nestedword.INwaOutgoingLetterAndTransitionProvider#isInitial(Object)
	 *         isInitial(state)} method is preferred.
	 */
	@Override
	Set<STATE> getInitialStates();

	/**
	 * @return The set of final states of this automaton. <b>Use with caution!</b> Some implementations (e.g., automaton
	 *         which represents result of a complementation) construct their set of states on the fly.
	 *         <p>
	 *         Although the result type is not a {@link Set}, the collection is guaranteed to not contain any
	 *         duplicates.
	 *         <p>
	 *         Using the
	 *         {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider# isFinal(Object)
	 *         isFinal(Object)} method to check if a specific state is final is preferred.
	 */
	Collection<STATE> getFinalStates();
	
	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing return transition labeled
	 *         with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersReturn(STATE state);

	/**
	 * @param state
	 *            state
	 * @return All letters <tt>a</tt> such that <tt>state</tt> has an incoming internal transition labeled with letter
	 *         <tt>a</tt>.
	 */
	Set<LETTER> lettersInternalIncoming(STATE state);

	/**
	 * @param state
	 *            state
	 * @return All letters <tt>a</tt> such that <tt>state</tt> has an incoming call transition labeled with letter
	 *         <tt>a</tt>.
	 */
	Set<LETTER> lettersCallIncoming(STATE state);

	/**
	 * @param state
	 *            state
	 * @return All letters a such that <tt>state</tt> has an incoming return transition labeled with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersReturnIncoming(STATE state);

	/**
	 * @param state
	 *            state
	 * @return All letters <tt>a</tt> such that <tt>state</tt> occurs as hierarchical predecessor state in a return
	 *         transition labeled with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersSummary(STATE state);

	/**
	 * All states <tt>hier</tt> such that <tt>state</tt> has an outgoing return transition
	 * <tt>(state, hier, letter, succ)</tt> for some state <tt>succ</tt>.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return hierarchical predecessor states for the given return letter
	 * @deprecated Inefficient, has to iterate over all outgoing transitions.
	 */
	@Deprecated
	default Iterable<STATE> hierarchicalPredecessorsOutgoing(final STATE state, final LETTER letter) {
		return NestedWordAutomataUtils.hierarchicalPredecessorsOutgoing(state, letter, this);
	}

	/**
	 * Incoming internal transitions for a given letter.
	 * 
	 * @param succ
	 *            successor state
	 * @param letter
	 *            letter
	 * @return incoming internal transitions
	 */
	Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ, final LETTER letter);

	/**
	 * Incoming internal transitions for all letters.
	 * 
	 * @param succ
	 *            successor state
	 * @return incoming internal transitions
	 */
	Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(final STATE succ);

	/**
	 * Incoming call transitions for a given letter.
	 * 
	 * @param succ
	 *            successor state
	 * @param letter
	 *            letter
	 * @return incoming call transitions
	 */
	Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ, final LETTER letter);

	/**
	 * Incoming call transitions for all letters.
	 * 
	 * @param succ
	 *            successor state
	 * @return incoming call transitions
	 */
	Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(final STATE succ);

	/**
	 * Incoming return transitions for a given hierarchical predecessor state and letter.
	 * 
	 * @param succ
	 *            successor state
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final STATE hier,
			final LETTER letter);

	/**
	 * Incoming return transitions for a given letter and all hierarchical predecessor states.
	 * 
	 * @param succ
	 *            successor state
	 * @param letter
	 *            letter
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ, final LETTER letter);

	/**
	 * Incoming return transitions for all letters and hierarchical predecessor states.
	 * 
	 * @param succ
	 *            successor state
	 * @return incoming return transitions
	 */
	Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(final STATE succ);

	/**
	 * Outgoing return transitions for a given letter and all hierarchical predecessor states.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return outgoing return transitions
	 * @deprecated Inefficient! try to iterate over all outgoing transitions
	 * or over all outgoing transitions that have a specific down state.
	 */
	@Deprecated
	default Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final LETTER letter) {
		return NestedWordAutomataUtils.returnSuccessors(state, letter, this);
	}

	/**
	 * Outgoing return transitions for all letters and hierarchical predecessor states.
	 * 
	 * @param state
	 *            state
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state);

	/**
	 * Summary transitions for a given letter and hierarchical predecessor state.
	 * 
	 * @param hier
	 *            hierarchical predecessor state
	 * @param letter
	 *            letter
	 * @return summary transitions
	 */
	Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier, final LETTER letter);

	/**
	 * Summary transitions for a given hierarchical predecessor state and all letters.
	 * 
	 * @param hier
	 *            hierarchical predecessor state
	 * @return summary transitions
	 */
	Iterable<SummaryReturnTransition<LETTER, STATE>> summarySuccessors(final STATE hier);
}
