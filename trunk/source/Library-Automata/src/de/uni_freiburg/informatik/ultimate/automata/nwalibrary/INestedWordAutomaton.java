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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Collection;
import java.util.Set;

/**
 * Interface for data structures that implement nested word automata.
 * (see INestedWordAutomatonSimple).
 * @author Matthias Heizmann
 *
 * @param <LETTER>
 * @param <STATE>
 */
public interface INestedWordAutomaton<LETTER, STATE> extends INestedWordAutomatonSimple<LETTER, STATE> {

	/**
	 * Returns the set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly.
	 */
	public Collection<STATE> getStates();

	/**
	 * Returns the set of initial states. 
	 */
	public Collection<STATE> getInitialStates();
	
	/**
	 * Returns the set of states of this automaton. <b>Use with caution!</b>
	 * Some implementations (e.g., automaton which represents result of
	 * a complementation) construct their set of states on the fly. Use the
	 * {@link isFinal} method to check if a specific state is final. 	
	 */
	public Collection<STATE> getFinalStates();

	/**
	 * @return All letters a such that state has an incoming internal 
	 * transition labeled with letter a.
	 */
	public Set<LETTER> lettersInternalIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming call 
	 * transition labeled with letter a.
	 */	
	public Set<LETTER> lettersCallIncoming(STATE state);
	
	/**
	 * @return All letters a such that state has an incoming return 
	 * transition labeled with letter a.
	 */		
	public Set<LETTER> lettersReturnIncoming(STATE state);
	
	/**
	 * @return All letters a such that state occurs as hierarchical predecessor
	 * in a return transition labeled with letter a.
	 */
	public Set<LETTER> lettersReturnSummary(STATE state);
	
	/**
	 * @return All states hier such that state has an outgoing 
	 * return transition (state, hier, letter, succ)
	 */
	public abstract Iterable<STATE> hierPred(STATE state, LETTER letter);

	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final LETTER letter, final STATE hier);
	
	public abstract Iterable<SummaryReturnTransition<LETTER, STATE>> returnSummarySuccessor(
			final STATE hier);

	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final STATE succ);
	
	public abstract Iterable<IncomingInternalTransition<LETTER, STATE>> internalPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final LETTER letter, final STATE succ);

	public abstract Iterable<IncomingCallTransition<LETTER, STATE>> callPredecessors(
			final STATE succ);

	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE hier, final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final LETTER letter, final STATE succ);
	
	public Iterable<IncomingReturnTransition<LETTER, STATE>> returnPredecessors(
			final STATE succ);
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final LETTER letter);
	
	
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state);
	
}