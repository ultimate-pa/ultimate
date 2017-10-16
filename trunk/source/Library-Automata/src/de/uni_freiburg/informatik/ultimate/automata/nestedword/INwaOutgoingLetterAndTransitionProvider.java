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

import java.util.Iterator;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.NestedIteratorNoopConstruction;

/**
 * Interface for the most basic data structure that represents a nested word automaton (NWA). This data structure
 * neither provides a method for getting all states nor for getting incoming transitions and hence allows us to have an
 * implementation that constructs automata on-demand (resp. lazily aka on-the-fly).
 * Classes that implement this interface do not have to store all transitions of the automaton explicitly.
 * Instead these classes only have to provide outgoing transitions for a given
 * state or a state/letter combination.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public interface INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> extends INwaOutgoingTransitionProvider<LETTER, STATE> {

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing internal transition labeled
	 *         with letter <tt>a</tt>.
	 */
	default Set<LETTER> lettersInternal(final STATE state) {
		return getVpAlphabet().getInternalAlphabet();
	}

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing call transition labeled with
	 *         letter <tt>a</tt>.
	 */
	default Set<LETTER> lettersCall(final STATE state) {
		return getVpAlphabet().getCallAlphabet();
	}

	/**
	 * @param state
	 *            state
	 * @return Superset of all letters <tt>a</tt> such that <tt>state</tt> has an outgoing return transition whose
	 * hierarchical predecessor is hier and that is labeled with letter <tt>a</tt> 
	 */
	default Set<LETTER> lettersReturn(final STATE state, final STATE hier) {
		return getVpAlphabet().getReturnAlphabet();
	}
	
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
	

	@Override
	default Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final Function<LETTER, Iterator<OutgoingInternalTransition<LETTER, STATE>>> fun = x -> internalSuccessors(state, x).iterator();
		return () -> new NestedIteratorNoopConstruction<LETTER, OutgoingInternalTransition<LETTER, STATE>>(lettersInternal(state).iterator(), fun);
	}

	@Override
	default Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		final Function<LETTER, Iterator<OutgoingCallTransition<LETTER, STATE>>> fun = x -> callSuccessors(state, x).iterator();
		return () -> new NestedIteratorNoopConstruction<LETTER, OutgoingCallTransition<LETTER, STATE>>(lettersCall(state).iterator(), fun);
	}

	@Override
	default Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state, final STATE hier) {
		final Function<LETTER, Iterator<OutgoingReturnTransition<LETTER, STATE>>> fun = x -> returnSuccessors(state, hier, x).iterator();
		return () -> new NestedIteratorNoopConstruction<LETTER, OutgoingReturnTransition<LETTER, STATE>>(lettersReturn(state, hier).iterator(), fun);
	}


}
