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

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Interface for the most basic data structure that represents a nested word 
 * automaton. This data structure neither provides a method for getting all
 * states nor for getting incoming transitions and hence allows an 
 * implementation that constructs automata lazily.
 * (See INestedWordAutomaton for an interface that provides these methods.)
 * 
 * <p>Nested word automata are a machine model which accepts nested words which
 * have been introduced by Alur et al.
 * [1] http://www.cis.upenn.edu/~alur/nw.html
 * [2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13
 * [3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)
 * 
 * <p>We stick to the definitions of [2] and deviate from [3] by using only one
 * kind of states (not hierarchical states and linear states).
 * 
 * <p>We also deviate form all common definitions of NWAs by specifying three Kinds
 * of Alphabets. The idea is that they do not have to be disjoint and allow to
 * totalize and complement the automaton with respect to this limitation of
 * which letter can occur in which kind of transition (which is convenient to
 * speed up applications where the automaton models a program and call
 * statements occur anyway only at call transitions).
 * If you want to use NWAs according to the common definition just use the same
 * alphabet as internal, call and return alphabet. 
 * 
 * @author heizmann@informatik.uni-freiburg.de
 *
 * @param <LETTER>
 * 		Type of Objects which can be used as letters of the alphabet.
 * @param <STATE>
 *		Type of Objects which can be used as states.
 */
public interface INestedWordAutomatonSimple<LETTER, STATE>
		extends IAutomaton<LETTER, STATE> {
	
	/**
	 * @return Set of all letters that can occur as label of an internal
	 *     transition. 
	 *     The default definition of nested word automata does not allow separate
	 *     alphabets for internal, call and return. The default definition of 
	 *     visibly pushdown automata requires that all three alphabets are disjoint.
	 *     We deviate from both definitions. We allow separate alphabets but do not
	 *     require that they are disjoint.
	 */
	Set<LETTER> getInternalAlphabet();


	/**
	 * @return Set of all letters that can occur as label of a call transition. 
	 *     The default definition of nested word automata does not allow separate
	 *     alphabets for internal, call and return. The default definition of 
	 *     visibly pushdown automata requires that all three alphabets are disjoint.
	 *     We deviate from both definitions. We allow separate alphabets but do not
	 *     require that they are disjoint.
	 */
	Set<LETTER> getCallAlphabet();


	/**
	 * @return Set of all letters that can occur as label of a return transition. 
	 *     The default definition of nested word automata does not allow separate
	 *     alphabets for internal, call and return. The default definition of 
	 *     visibly pushdown automata requires that all three alphabets are disjoint.
	 *     We deviate from both definitions. We allow separate alphabets but do not
	 *     require that they are disjoint.
	 */
	Set<LETTER> getReturnAlphabet();
	
	
	/**
	 * @return The StateFactory which was used to construct the states of this
	 *     automaton.
	 */
	@Override
	StateFactory<STATE> getStateFactory();
	
	
	/**
	 * @return Auxiliary state used to model the hierarchical predecessor of a
	 *     pending return in some operations. Recall that we generally do not accept nested
	 *     word with pending returns. This auxiliary state is <i>never</i> contained
	 *     is the set of states.
	 *     Viewing nested word automata as visibly pushdown automata this state can
	 *     be seen as a "bottom letter" of the pushdown alphabet.
	 */
	STATE getEmptyStackState();
	

	/**
	 * @return All initial states of automaton. 
	 */
	Iterable<STATE> getInitialStates();
	
	/**
	 * @param state state
	 * @return true iff state is initial.
	 */
	boolean isInitial(STATE state);
	
	
	/**
	 * @param state state
	 * @return true iff state is final.
	 */
	boolean isFinal(STATE state);

	/**
	 * @param state state
	 * @return Superset of all letters a such that state has an outgoing
	 *     internal transition labeled with letter a.
	 */
	Set<LETTER> lettersInternal(STATE state);
	
	/**
	 * @param state state
	 * @return Superset of all letters a such that state has an outgoing call
	 *     transition labeled with letter a.
	 */	
	Set<LETTER> lettersCall(STATE state);
	
	/**
	 * @param state state
	 * @return Superset of all letters a such that state has an outgoing return 
	 *     transition labeled with letter a.
	 */		
	Set<LETTER> lettersReturn(STATE state);

	/**
	 * @param state state
	 * @param letter letter
	 * @return outgoing transitions
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state, final LETTER letter);

	/**
	 * @param state state
	 * @return outgoing transitions
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(
			final STATE state);

	/**
	 * @param state state
	 * @param letter letter
	 * @return outgoing transitions
	 */
	Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state, final LETTER letter);

	/**
	 * @param state state
	 * @return outgoing transitions
	 */
	Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(
			final STATE state);
	
	/**
	 * @param state state
	 * @param hier hierarchical predecessor
	 * @param letter letter
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(
			final STATE state, final STATE hier, final LETTER letter);
	
	/**
	 * @param state state
	 * @param hier hierarchical predecessor
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(
			final STATE state, final STATE hier);
}
