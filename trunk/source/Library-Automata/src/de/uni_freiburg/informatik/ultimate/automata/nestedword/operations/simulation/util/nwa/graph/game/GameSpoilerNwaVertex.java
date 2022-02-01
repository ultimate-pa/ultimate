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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SpoilerNwaVertex;

/**
 * Wrapper that represents a Spoiler vertex as game automaton state.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class GameSpoilerNwaVertex<LETTER, STATE> implements IGameState {

	/**
	 * The Spoiler vertex represented by this wrapper.
	 */
	private final SpoilerNwaVertex<LETTER, STATE> mSpoilerNwaVertex;

	/**
	 * Creates a new game automaton state that represents the given Spoiler vertex.
	 * 
	 * @param spoilerNwaVertex
	 *            The Spoiler vertex represented by this wrapper
	 */
	public GameSpoilerNwaVertex(final SpoilerNwaVertex<LETTER, STATE> spoilerNwaVertex) {
		super();
		mSpoilerNwaVertex = spoilerNwaVertex;
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
		if (!(obj instanceof GameSpoilerNwaVertex)) {
			return false;
		}
		final GameSpoilerNwaVertex<?, ?> other = (GameSpoilerNwaVertex<?, ?>) obj;
		if (mSpoilerNwaVertex == null) {
			if (other.mSpoilerNwaVertex != null) {
				return false;
			}
		} else if (!mSpoilerNwaVertex.equals(other.mSpoilerNwaVertex)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the Spoiler vertex represented by this wrapper.
	 * 
	 * @return The Spoiler vertex represented by this wrapper
	 */
	public SpoilerNwaVertex<LETTER, STATE> getSpoilerNwaVertex() {
		return mSpoilerNwaVertex;
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
		result = prime * result + ((mSpoilerNwaVertex == null) ? 0 : mSpoilerNwaVertex.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return mSpoilerNwaVertex.toString();
	}

}
