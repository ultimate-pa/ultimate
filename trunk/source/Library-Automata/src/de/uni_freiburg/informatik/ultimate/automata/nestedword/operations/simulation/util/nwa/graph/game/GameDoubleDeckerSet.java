/*
 * Copyright (C) 2015-2016 Daniel Tischner
 * Copyright (C) 2009-2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.game;

import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * Wrapper that represents a double decker set of a game automaton. They assign multiply up states to each down state.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class GameDoubleDeckerSet implements IGameState {

	/**
	 * Provides a fast access to the up states via their associated down state.
	 */
	private final Map<IGameState, Set<IGameState>> mDownToUp;

	/**
	 * Creates a new game automaton state that represents a double decker set.
	 * 
	 * @param downToUp
	 *            Maps each down state to a set of up states
	 */
	public GameDoubleDeckerSet(final Map<IGameState, Set<IGameState>> downToUp) {
		super();
		mDownToUp = downToUp;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (!(obj instanceof GameDoubleDeckerSet)) {
			return false;
		}
		final GameDoubleDeckerSet other = (GameDoubleDeckerSet) obj;
		if (mDownToUp == null) {
			if (other.mDownToUp != null) {
				return false;
			}
		} else if (!mDownToUp.equals(other.mDownToUp)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the down states of this double decker, they are used as key for the up states.
	 * 
	 * @return The down states of this double decker
	 */
	public Set<IGameState> getDownStates() {
		return mDownToUp.keySet();
	}

	/**
	 * Gets the up states of this double decker that are associated to the given down state.
	 * 
	 * @param downState
	 *            Down state associated to the up states to get
	 * @return The up states of this double decker that are associated to the given down state
	 */
	public Set<IGameState> getUpStates(final IGameState downState) {
		return mDownToUp.get(downState);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDownToUp == null) ? 0 : mDownToUp.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		sb.append("{");
		for (final IGameState down : mDownToUp.keySet()) {
			final Iterator<IGameState> it = mDownToUp.get(down).iterator();
			IGameState up = it.next();
			sb.append("(").append(down).append(",").append(up).append(")");
			while (it.hasNext()) {
				up = it.next();
				sb.append(", ");
				sb.append("(").append(down).append(",").append(up).append(")");
			}
		}
		sb.append("}");
		return sb.toString();
	}
}
