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

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;

/**
 * Element for a breadth-first search that computes the priority of a given
 * summarize edge based on the priorities of vertices in the game graph.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SearchElement<LETTER, STATE> {
	/**
	 * Creates a new search element with a given vertex and a vertex which
	 * specifies the down state.
	 * 
	 * @param vertex
	 *            Vertex for the search element
	 * @param downStateVertex
	 *            Vertex that specifies the down state. The down state is (q0,
	 *            q1).
	 * @return The corresponding created search element.
	 */
	public static <LETTER, STATE> SearchElement<LETTER, STATE> createRootSearchElement(
			final Vertex<LETTER, STATE> vertex, final Vertex<LETTER, STATE> downStateVertex) {
		return new SearchElement<LETTER, STATE>(vertex,
				new VertexDownState<STATE>(downStateVertex.getQ0(), downStateVertex.getQ1()));
	}

	/**
	 * Extracts the vertex double decker representation from a given search
	 * element.
	 * 
	 * @param searchElement
	 *            Search element to extract from
	 * @return The vertex double decker representation of the given search
	 *         element.
	 */
	public static <LETTER, STATE> VertexDoubleDecker<STATE> extractVertexDoubleDecker(
			final SearchElement<LETTER, STATE> searchElement) {
		Vertex<LETTER, STATE> vertex = searchElement.getVertex();
		VertexUpState<STATE> upState = new VertexUpState<STATE>(vertex.getQ0(), vertex.getQ1());
		return new VertexDoubleDecker<>(upState, searchElement.getDownState());
	}

	/**
	 * The down state of this element.
	 */
	private final VertexDownState<STATE> m_DownState;
	/**
	 * The vertex of this element.
	 */
	private final Vertex<LETTER, STATE> m_Vertex;

	/**
	 * Creates a new search element with a given vertex and a down state. Together they form a double decker vertex.
	 * 
	 * @param vertex
	 *            Vertex for this element
	 * @param downState
	 *            Down state for this element
	 */
	public SearchElement(final Vertex<LETTER, STATE> vertex, final VertexDownState<STATE> downState) {
		m_Vertex = vertex;
		m_DownState = downState;
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
		if (!(obj instanceof SearchElement)) {
			return false;
		}
		SearchElement<?, ?> other = (SearchElement<?, ?>) obj;
		if (m_DownState == null) {
			if (other.m_DownState != null) {
				return false;
			}
		} else if (!m_DownState.equals(other.m_DownState)) {
			return false;
		}
		if (m_Vertex == null) {
			if (other.m_Vertex != null) {
				return false;
			}
		} else if (!m_Vertex.equals(other.m_Vertex)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the down state.
	 * 
	 * @return The down state
	 */
	public VertexDownState<STATE> getDownState() {
		return m_DownState;
	}

	/**
	 * Gets the vertex.
	 * 
	 * @return The vertex
	 */
	public Vertex<LETTER, STATE> getVertex() {
		return m_Vertex;
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
		result = prime * result + ((m_DownState == null) ? 0 : m_DownState.hashCode());
		result = prime * result + ((m_Vertex == null) ? 0 : m_Vertex.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "SearchElement [m_DownState=" + m_DownState + ", m_Vertex=" + m_Vertex + "]";
	}
}
