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
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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
		final Vertex<LETTER, STATE> vertex = searchElement.getVertex();
		final VertexUpState<STATE> upState = new VertexUpState<STATE>(vertex.getQ0(), vertex.getQ1());
		return new VertexDoubleDecker<>(upState, searchElement.getDownState());
	}

	/**
	 * The down state of this element.
	 */
	private final VertexDownState<STATE> mDownState;
	/**
	 * Vertex down state that was used right before this search element.
	 */
	private final VertexDownState<STATE> mHistory;
	/**
	 * Summarize edge this element corresponds to.
	 */
	private final SummarizeEdge<LETTER, STATE> mSummarizeEdge;
	/**
	 * The vertex of this element.
	 */
	private final Vertex<LETTER, STATE> mVertex;

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
		mVertex = vertex;
		mDownState = downState;
		mHistory = history;
		mSummarizeEdge = summarizeEdge;
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
		final SearchElement<?, ?> other = (SearchElement<?, ?>) obj;
		if (mDownState == null) {
			if (other.mDownState != null) {
				return false;
			}
		} else if (!mDownState.equals(other.mDownState)) {
			return false;
		}
		if (mVertex == null) {
			if (other.mVertex != null) {
				return false;
			}
		} else if (!mVertex.equals(other.mVertex)) {
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
		return mDownState;
	}

	/**
	 * Gets the vertex down state that was used right before this search
	 * element.
	 * 
	 * @return The vertex down state that was used right before this search
	 *         element.
	 */
	public VertexDownState<STATE> getHistory() {
		return mHistory;
	}

	/**
	 * Gets the summarize edge this element corresponds to.
	 * 
	 * @return The summarize edge this element corresponds to or <tt>null</tt>
	 *         if not set.
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return mSummarizeEdge;
	}

	/**
	 * Gets the vertex.
	 * 
	 * @return The vertex
	 */
	public Vertex<LETTER, STATE> getVertex() {
		return mVertex;
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
		result = prime * result + ((mDownState == null) ? 0 : mDownState.hashCode());
		result = prime * result + ((mVertex == null) ? 0 : mVertex.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "SearchElement [mDownState=" + mDownState + ", mVertex=" + mVertex + "]";
	}
}
