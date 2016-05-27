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
 * Interface for objects that have a {@link VertexDownState}.
 * 
 * @author Daniel Tischner
 *
 * @param <STATE>
 *            State class of nwa automaton
 */
public interface IHasVertexDownStates<STATE> {
	/**
	 * Gets the vertex down states of this object.
	 * 
	 * @return The vertex down states of this object.
	 */
	public VertexDownState<STATE> getVertexDownState();

	/**
	 * Returns if the object has a given vertex down state.
	 * 
	 * @param leftDownState
	 *            Left state of the down state configuration
	 * @param rightDownState
	 *            Right state of the down state configuration
	 * @return If the object has the given down state configuration
	 */
	public boolean hasVertexDownState(final STATE leftDownState, final STATE rightDownState);

	/**
	 * Returns if the object has a given vertex down state.
	 * 
	 * @param vertexDownState
	 *            Down state configuration in ask
	 * @return If the object has the given down state configuration
	 */
	public boolean hasVertexDownState(final VertexDownState<STATE> vertexDownState);

	/**
	 * Returns whether the given vertex down state is marked as safe or not.
	 * 
	 * @return Whether the given vertex down state is marked as safe or not.
	 */
	public Boolean isVertexDownStateSafe();

	/**
	 * Sets whether the given vertex down state is marked as safe or not.
	 * 
	 * @param isSafe
	 *            Whether the given vertex down state should be marked as safe
	 *            or not
	 */
	public void setVertexDownStateSafe(final boolean isSafe);
}
