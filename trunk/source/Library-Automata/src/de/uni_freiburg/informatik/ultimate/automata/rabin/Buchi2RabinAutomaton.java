/*
 * Copyright (C) 2023 Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.rabin;

import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;

/**
 * Wraps a Büchi-automton (represented by {@link INwaOutgoingLetterAndTransitionProvider}) into an
 * {@link IRabinAutomaton}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class Buchi2RabinAutomaton<LETTER, STATE> implements IRabinAutomaton<LETTER, STATE> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mUnderlying;

	public Buchi2RabinAutomaton(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> underlying) {
		// TODO: Should we check that underlying has no call/return edges?
		mUnderlying = underlying;
	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mUnderlying.getAlphabet();
	}

	@Override
	public int size() {
		return mUnderlying.size();
	}

	@Override
	public String sizeInformation() {
		return mUnderlying.sizeInformation();
	}

	@Override
	public Set<STATE> getInitialStates() {
		return StreamSupport.stream(mUnderlying.getInitialStates().spliterator(), false).collect(Collectors.toSet());
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mUnderlying.isInitial(state);
	}

	@Override
	public boolean isAccepting(final STATE state) {
		return mUnderlying.isFinal(state);
	}

	@Override
	public boolean isFinite(final STATE state) {
		return false;
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state) {
		return mUnderlying.internalSuccessors(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> getSuccessors(final STATE state, final LETTER letter) {
		return mUnderlying.internalSuccessors(state, letter);
	}
}
