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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public abstract class FullMultipebbleGameState<STATE> {

	protected final DoubleDecker<STATE> mSpoilerDoubleDecker;

	public FullMultipebbleGameState(final DoubleDecker<STATE> spoilerDoubleDecker) {
		mSpoilerDoubleDecker = spoilerDoubleDecker;
	}

	public DoubleDecker<STATE> getSpoilerDoubleDecker() {
		return mSpoilerDoubleDecker;
	}

	public abstract boolean isAccepting();

	public abstract int getNumberOfDoubleDeckerPebbles();

	protected <LETTER> List<DoubleDecker<STATE>> computeSpoilerSuccessorsInternal(final LETTER letter,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		final List<DoubleDecker<STATE>> result = new ArrayList<>();
		for (final OutgoingInternalTransition<LETTER, STATE> trans : nwa
				.internalSuccessors(mSpoilerDoubleDecker.getUp(), letter)) {
			result.add(new DoubleDecker<>(mSpoilerDoubleDecker.getDown(), trans.getSucc()));
		}
		return result;
	}

	protected <LETTER> List<DoubleDecker<STATE>> computeSpoilerSuccessorsCall(final LETTER letter,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		final List<DoubleDecker<STATE>> result = new ArrayList<>();
		for (final OutgoingCallTransition<LETTER, STATE> trans : nwa.callSuccessors(mSpoilerDoubleDecker.getUp(),
				letter)) {
			result.add(new DoubleDecker<>(mSpoilerDoubleDecker.getUp(), trans.getSucc()));
		}
		return result;
	}

	protected <LETTER> List<DoubleDecker<STATE>> computeSpoilerSuccessorsReturn(final DoubleDecker<STATE> hier,
			final LETTER letter, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> nwa) {
		if (!hier.getUp().equals(mSpoilerDoubleDecker.getDown())) {
			throw new IllegalArgumentException("mismatch");
		}
		final List<DoubleDecker<STATE>> result = new ArrayList<>();
		for (final OutgoingReturnTransition<LETTER, STATE> trans : nwa.returnSuccessors(mSpoilerDoubleDecker.getUp(),
				mSpoilerDoubleDecker.getDown(), letter)) {
			result.add(new DoubleDecker<>(hier.getDown(), trans.getSucc()));
		}
		return result;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mSpoilerDoubleDecker == null) ? 0 : mSpoilerDoubleDecker.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final FullMultipebbleGameState<?> other = (FullMultipebbleGameState<?>) obj;
		if (mSpoilerDoubleDecker == null) {
			if (other.mSpoilerDoubleDecker != null) {
				return false;
			}
		} else if (!mSpoilerDoubleDecker.equals(other.mSpoilerDoubleDecker)) {
			return false;
		}
		return true;
	}

}
