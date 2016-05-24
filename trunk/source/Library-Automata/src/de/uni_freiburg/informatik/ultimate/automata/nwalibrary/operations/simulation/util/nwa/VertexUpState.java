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
 * Container that holds a left and a right up state. Game graph vertices have
 * a left and right up state, this container is used to represent those states.
 * 
 * @author Daniel Tischner
 *
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class VertexUpState<STATE> {

	/**
	 * Left up state of the vertex.
	 */
	private final STATE mLeftUpState;
	/**
	 * Right up state of the vertex.
	 */
	private final STATE mRightUpState;

	/**
	 * Creates a new vertex up state with two given up states.
	 * 
	 * @param leftUpState
	 *            Left up state of the vertex
	 * @param rightUpState
	 *            Right up state of the vertex
	 */
	public VertexUpState(final STATE leftUpState, final STATE rightUpState) {
		mLeftUpState = leftUpState;
		mRightUpState = rightUpState;
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
		if (!(obj instanceof VertexUpState)) {
			return false;
		}
		VertexUpState<?> other = (VertexUpState<?>) obj;
		if (mLeftUpState == null) {
			if (other.mLeftUpState != null) {
				return false;
			}
		} else if (!mLeftUpState.equals(other.mLeftUpState)) {
			return false;
		}
		if (mRightUpState == null) {
			if (other.mRightUpState != null) {
				return false;
			}
		} else if (!mRightUpState.equals(other.mRightUpState)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the left up state of the vertex.
	 * 
	 * @return The left up state
	 */
	public STATE getLeftUpState() {
		return mLeftUpState;
	}

	/**
	 * Gets the right up state of the vertex.
	 * 
	 * @return The right up state
	 */
	public STATE getRightUpState() {
		return mRightUpState;
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
		result = prime * result + ((mLeftUpState == null) ? 0 : mLeftUpState.hashCode());
		result = prime * result + ((mRightUpState == null) ? 0 : mRightUpState.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "[" + mLeftUpState + "," + mRightUpState + "]";
	}
}
