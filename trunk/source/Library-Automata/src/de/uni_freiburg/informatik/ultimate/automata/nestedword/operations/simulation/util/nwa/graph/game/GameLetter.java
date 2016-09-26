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

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.ETransitionType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.DuplicatorNwaVertex;

/**
 * Represents a letter in a game automaton. Such a letter is a Duplicator
 * game graph node.
 * 
 * @author Daniel Tischner
 * @author Matthias Heizmann
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class GameLetter<LETTER, STATE> {

	private final DuplicatorNwaVertex<LETTER, STATE> mDuplicatorNwaVertex;
	/**
	 * The transition type represented by this game letter.
	 */
	private final ETransitionType mTransitionType;


	/**
	 * @param transitionType
	 *            The transition type represented by this game letter
	 */
	public GameLetter(final DuplicatorNwaVertex<LETTER, STATE> duplicatorNwaVertex, final ETransitionType transitionType) {
		mDuplicatorNwaVertex = duplicatorNwaVertex;
		mTransitionType = transitionType;
	}

	/**
	 * Gets the letter used by Spoiler.
	 * 
	 * @return The letter used by Spoiler.
	 */
	public LETTER getLetter() {
		return mDuplicatorNwaVertex.getLetter();
	}

	/**
	 * Gets the destination of Spoiler.
	 * 
	 * @return The destination of Spoiler.
	 */
	public STATE getState() {
		return mDuplicatorNwaVertex.getQ0();
	}

	/**
	 * Gets the transition type represented by this game letter.
	 * 
	 * @return The transition type represented by this game letter
	 */
	public ETransitionType getTransitionType() {
		return mTransitionType;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mDuplicatorNwaVertex == null) ? 0 : mDuplicatorNwaVertex.hashCode());
		result = prime * result + ((mTransitionType == null) ? 0 : mTransitionType.hashCode());
		return result;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(final Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		final GameLetter other = (GameLetter) obj;
		if (mDuplicatorNwaVertex == null) {
			if (other.mDuplicatorNwaVertex != null)
				return false;
		} else if (!mDuplicatorNwaVertex.equals(other.mDuplicatorNwaVertex))
			return false;
		if (mTransitionType != other.mTransitionType)
			return false;
		return true;
	}

	/* (non-Javadoc)
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return mDuplicatorNwaVertex.toString();
	}

	
	

}
