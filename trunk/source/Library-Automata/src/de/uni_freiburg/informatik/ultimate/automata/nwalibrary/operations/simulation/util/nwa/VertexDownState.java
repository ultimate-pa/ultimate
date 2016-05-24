/*
 * Copyright (C) 2015-2016 Daniel Tischner
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.nwa;

/**
 * Container that holds a left and a right down state. Game graph vertices have
 * a left and right up state, this container is used to represent its down
 * states.
 * 
 * @author Daniel Tischner
 *
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class VertexDownState<STATE> {

	/**
	 * Left down state of the vertex.
	 */
	private final STATE mLeftDownState;
	/**
	 * Right down state of the vertex.
	 */
	private final STATE mRightDownState;

	/**
	 * Creates a new vertex down state with two given down states.
	 * 
	 * @param leftDownState
	 *            Left down state of the vertex
	 * @param rightDownState
	 *            Right down state of the vertex
	 */
	public VertexDownState(final STATE leftDownState, final STATE rightDownState) {
		mLeftDownState = leftDownState;
		mRightDownState = rightDownState;
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
		if (!(obj instanceof VertexDownState)) {
			return false;
		}
		VertexDownState<?> other = (VertexDownState<?>) obj;
		if (mLeftDownState == null) {
			if (other.mLeftDownState != null) {
				return false;
			}
		} else if (!mLeftDownState.equals(other.mLeftDownState)) {
			return false;
		}
		if (mRightDownState == null) {
			if (other.mRightDownState != null) {
				return false;
			}
		} else if (!mRightDownState.equals(other.mRightDownState)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the left down state of the vertex.
	 * 
	 * @return The left down state
	 */
	public STATE getLeftDownState() {
		return mLeftDownState;
	}

	/**
	 * Gets the right down state of the vertex.
	 * 
	 * @return The right down state
	 */
	public STATE getRightDownState() {
		return mRightDownState;
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
		result = prime * result + ((mLeftDownState == null) ? 0 : mLeftDownState.hashCode());
		result = prime * result + ((mRightDownState == null) ? 0 : mRightDownState.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + mLeftDownState + "," + mRightDownState + "]";
	}
}
