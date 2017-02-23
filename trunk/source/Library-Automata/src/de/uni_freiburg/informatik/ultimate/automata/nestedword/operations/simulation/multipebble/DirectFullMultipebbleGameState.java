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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.HashRelation;

/**
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <STATE>
 *            state type
 */
public class DirectFullMultipebbleGameState<STATE> extends FullMultipebbleGameState<STATE> {
	private final HashRelation<STATE, STATE> mDuplicatorDoubleDeckers;

	public DirectFullMultipebbleGameState(final DoubleDecker<STATE> spoilerDoubleDecker,
			final HashRelation<STATE, STATE> duplicatorDoubleDeckers) {
		super(spoilerDoubleDecker);
		mDuplicatorDoubleDeckers = duplicatorDoubleDeckers;
	}

	public HashRelation<STATE, STATE> getDuplicatorDoubleDeckers() {
		return mDuplicatorDoubleDeckers;
	}

	@Override
	public boolean isAccepting() {
		return mDuplicatorDoubleDeckers.isEmpty();
	}

	@Override
	public int getNumberOfDoubleDeckerPebbles() {
		return mDuplicatorDoubleDeckers.size();
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((mDuplicatorDoubleDeckers == null) ? 0 : mDuplicatorDoubleDeckers.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!super.equals(obj)) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final DirectFullMultipebbleGameState<?> other = (DirectFullMultipebbleGameState<?>) obj;
		if (mDuplicatorDoubleDeckers == null) {
			if (other.mDuplicatorDoubleDeckers != null) {
				return false;
			}
		} else if (!mDuplicatorDoubleDeckers.equals(other.mDuplicatorDoubleDeckers)) {
			return false;
		}
		return true;
	}

	@Override
	public String toString() {
		return "Spoiler: " + mSpoilerDoubleDecker + " Duplicator: " + mDuplicatorDoubleDeckers;
	}

}
