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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Interface for the most basic data structure that represents a nested word
 * automaton (NWA). This data structure neither provides a method for getting all
 * states nor for getting incoming transitions and hence allows an
 * implementation that constructs automata lazily.
 * (See {@link INestedWordAutomaton} for an interface that provides these methods.)
 * <p>
 * A nested word automaton is a machine model which accepts nested words (see {@link NestedWord})
 * introduced by Alur et al.
 * <ul>
 * <li>[1] http://www.cis.upenn.edu/~alur/nw.html</li>
 * <li>[2] Rajeev Alur, P. Madhusudan: Adding Nesting Structure to Words. Developments in Language Theory 2006:1-13</li>
 * <li>[3] Rajeev Alur, P. Madhusudan: Adding nesting structure to words. J. ACM (JACM) 56(3) (2009)</li>
 * </ul>
 * We stick to the definitions of [2] and deviate from [3] by using only one
 * kind of states (instead of a separation of hierarchical states and linear states).
 * <p>
 * We also deviate from all common definitions of NWA by specifying three kinds
 * of Alphabets. The idea is that they do not have to be disjoint and allow to
 * totalize and complement the automaton with respect to the limitation of
 * which letter can occur in which kind of transition (which is convenient to
 * speed up applications where the automaton models a program and call
 * statements occur anyway only at call transitions).
 * If a user wants to use NWA according to the common definition, they should just use the same
 * set for the internal, call, and return alphabet.
 * <p>
 * Another deviation from the general model is that we generally do not accept nested words with pending returns. We do
 * accept, however, nested words with pending calls.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public interface INestedWordAutomatonSimple<LETTER, STATE> extends IAutomaton<LETTER, STATE> {
	/**
	 * @return Set of all letters that can occur as label of an internal transition.
	 *         <p>
	 *         The default definition of nested word automata does not allow separate
	 *         alphabets for internal, call, and return symbols. The default definition of
	 *         visibly pushdown automata requires that all three alphabets are disjoint.
	 *         We deviate from both definitions. We allow separate alphabets but do not
	 *         require that they are disjoint.
	 */
	Set<LETTER> getInternalAlphabet();

	/**
	 * @return Set of all letters that can occur as label of a call transition.
	 * @see #getInternalAlphabet()
	 */
	Set<LETTER> getCallAlphabet();

	/**
	 * @return Set of all letters that can occur as label of a return transition.
	 * @see #getInternalAlphabet()
	 */
	Set<LETTER> getReturnAlphabet();

	/**
	 * @return Auxiliary state used to model the hierarchical predecessor of a
	 *         pending return in some operations.<br>
	 *         Recall that we generally do not accept nested
	 *         words with pending returns. This auxiliary state is <i>never</i> contained
	 *         in the set of states.
	 *         Viewing nested word automata as visibly pushdown automata, this state can
	 *         be seen as a "bottom letter" of the pushdown alphabet.
	 */
	STATE getEmptyStackState();

	/**
	 * @return All initial states of the automaton.
	 */
	Iterable<STATE> getInitialStates();

	/**
	 * @param state
	 *            state
	 * @return true iff the state is initial.
	 */
	boolean isInitial(STATE state);

	/**
	 * @param state
	 *            state
	 * @return true iff the state is final.
	 */
	boolean isFinal(STATE state);

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing
	 *         internal transition labeled with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersInternal(STATE state);

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing call
	 *         transition labeled with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersCall(STATE state);

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing return
	 *         transition labeled with letter <tt>a</tt>.
	 */
	Set<LETTER> lettersReturn(STATE state);

	/**
	 * All internal successor transitions for a given state and letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return outgoing internal transitions
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state, final LETTER letter);

	/**
	 * All internal successor transitions for a given state.
	 * 
	 * @param state
	 *            state
	 * @return outgoing internal transitions
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state);

	/**
	 * All call successor transitions for a given state and letter.
	 * 
	 * @param state
	 *            state
	 * @param letter
	 *            letter
	 * @return outgoing call transitions
	 */
	Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state, final LETTER letter);

	/**
	 * All call successor transitions for a given state.
	 * 
	 * @param state
	 *            state
	 * @return outgoing call transitions
	 */
	Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state);

	/**
	 * All return successor transitions for a given state, hierarchical predecessor, and letter.
	 * 
	 * @param state
	 *            state
	 * @param hier
	 *            hierarchical predecessor
	 * @param letter
	 *            letter
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessors(final STATE state, final STATE hier,
			final LETTER letter);

	/**
	 * All return successor transitions for a given state and hierarchical predecessor.
	 * 
	 * @param state
	 *            state
	 * @param hier
	 *            hierarchical predecessor
	 * @return outgoing return transitions
	 */
	Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state, final STATE hier);

	@Override
	default IElement transformToUltimateModel(final AutomataLibraryServices services)
			throws AutomataOperationCanceledException {
		return new NwaToUltimateModel<LETTER, STATE>(services).transformToUltimateModel(this);
	}
}
