/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * Supports all methods that are required by {@link NestedWordAutomatonReachableStates} which is able to transform
 * objects of this class into an {@link IDoubleDeckerAutomaton}. Who implements this class must only define outgoing
 * letters and successors for letters.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public abstract class NestedWordAutomatonForLetterBasedOnDemandConstruction<LETTER, STATE>
		implements INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> {

	@Override
	public final Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final List<OutgoingInternalTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final LETTER letter : lettersInternal(state)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : internalSuccessors(state, letter)) {
				result.add(trans);
			}
		}
		return result;
	}

	@Override
	public final Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		final List<OutgoingCallTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final LETTER letter : lettersCall(state)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : callSuccessors(state, letter)) {
				result.add(trans);
			}
		}
		return result;
	}

	@Override
	public final Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		final List<OutgoingReturnTransition<LETTER, STATE>> result = new ArrayList<>();
		for (final LETTER letter : lettersReturn(state, hier)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : returnSuccessors(state, hier, letter)) {
				result.add(trans);
			}
		}
		return result;
	}

}
