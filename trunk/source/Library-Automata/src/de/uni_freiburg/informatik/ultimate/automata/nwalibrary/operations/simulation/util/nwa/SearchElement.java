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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

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
	 * Computes and returns the summarize edge which corresponds to a double
	 * decker, given by a vertex and its down state. If the double decker does
	 * not directly corresponds to an edge, it assumes that the double decker
	 * corresponds to the previous summarize edge.
	 * 
	 * @param vertex
	 *            Vertex to compute its corresponding summarize edge
	 * @param downState
	 *            Down state of the vertex to compute its corresponding
	 *            summarize edge
	 * @param previousEdge
	 *            Summarize edge the predecessor of this double decker
	 *            corresponded to, <tt>null</tt> if there is no.
	 * @return The summarize edge corresponding to the given double decker,
	 *         <tt>previousEdge</tt> if there is no.
	 */
	public static <LETTER, STATE> SummarizeEdge<LETTER, STATE> computeSummarizeEdge(final Vertex<LETTER, STATE> vertex,
			final VertexDownState<STATE> downState, final SummarizeEdge<LETTER, STATE> previousEdge,
			final Map<Pair<Vertex<LETTER, STATE>, VertexDownState<STATE>>, SummarizeEdge<LETTER, STATE>> invokerToSummarizeEdge) {
		SummarizeEdge<LETTER, STATE> correspondingSummarizeEdge = invokerToSummarizeEdge
				.get(new Pair<>(vertex, downState));
		if (correspondingSummarizeEdge == null) {
			correspondingSummarizeEdge = previousEdge;
		}
		return correspondingSummarizeEdge;
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
	 * Vertex down state that was used right before this search element.
	 */
	private final VertexDownState<STATE> m_History;
	/**
	 * Summarize edge this element corresponds to.
	 */
	private final SummarizeEdge<LETTER, STATE> m_SummarizeEdge;
	/**
	 * The vertex of this element.
	 */
	private final Vertex<LETTER, STATE> m_Vertex;

	/**
	 * Creates a new search element with a given vertex and a down state.
	 * Together they form a double decker vertex.
	 * 
	 * @param vertex
	 *            Vertex for this element
	 * @param downState
	 *            Down state for this element
	 */
	public SearchElement(final Vertex<LETTER, STATE> vertex, final VertexDownState<STATE> downState) {
		this(vertex, downState, null, null);
	}

	/**
	 * Creates a new search element with a given vertex, a down state, a history
	 * element and the corresponding summarize edge. Together they form a double
	 * decker vertex.
	 * 
	 * @param vertex
	 *            Vertex for this element
	 * @param downState
	 *            Down state for this element
	 * @param history
	 *            Vertex down state that was used right before this search
	 *            element
	 * @param summarizeEdge
	 *            Summarize edge this element corresponds to
	 */
	public SearchElement(final Vertex<LETTER, STATE> vertex, final VertexDownState<STATE> downState,
			final VertexDownState<STATE> history, final SummarizeEdge<LETTER, STATE> summarizeEdge) {
		m_Vertex = vertex;
		m_DownState = downState;
		m_History = history;
		m_SummarizeEdge = summarizeEdge;
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
	 * Gets the vertex down state that was used right before this search
	 * element.
	 * 
	 * @return The vertex down state that was used right before this search
	 *         element.
	 */
	public VertexDownState<STATE> getHistory() {
		return m_History;
	}

	/**
	 * Gets the summarize edge this element corresponds to.
	 * 
	 * @return The summarize edge this element corresponds to or <tt>null</tt>
	 *         if not set.
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return m_SummarizeEdge;
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
