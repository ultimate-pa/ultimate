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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.visualization.NwaToUltimateModel;
import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

/**
 * Interface for a Nested Word Automaton that is defined by its outgoing 
 * transitions. Outgoing transitions are sufficient for the {@link NestedWordAutomatonReachableStates}
 * to construct a {@link IDoubleDeckerAutomaton}
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public interface INwaOutgoingTransitionProvider<LETTER, STATE> extends IAutomaton<LETTER, STATE> {
	/**
	 * @return Set of all letters that can occur as label of an internal transition.
	 *         <p>
	 *         The default definition of nested word automata does not allow separate alphabets for internal, call, and
	 *         return symbols. The default definition of visibly pushdown automata requires that all three alphabets are
	 *         disjoint. We deviate from both definitions. We allow separate alphabets but do not require that they are
	 *         disjoint.
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
	 * @return Auxiliary state used to model the hierarchical predecessor of a pending return in some operations.<br>
	 *         Recall that we generally do not accept nested words with pending returns. This auxiliary state is
	 *         <i>never</i> contained in the set of states. Viewing nested word automata as visibly pushdown automata,
	 *         this state can be seen as a "bottom letter" of the pushdown alphabet.
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
	 * All internal successor transitions for a given state.
	 * 
	 * @param state
	 *            state
	 * @return outgoing internal transitions
	 */
	Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state);

	/**
	 * All call successor transitions for a given state.
	 * 
	 * @param state
	 *            state
	 * @return outgoing call transitions
	 */
	Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state);

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
}
