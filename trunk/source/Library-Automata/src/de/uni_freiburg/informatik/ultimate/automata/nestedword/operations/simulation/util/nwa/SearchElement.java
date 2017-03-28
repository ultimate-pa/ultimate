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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.nwa.graph.SummarizeEdge;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Element for a breadth-first search that computes the priority of a given summarize edge based on the priorities of
 * vertices in the game graph.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SearchElement<LETTER, STATE> {
	/**
	 * The choice Duplicator made in the summarize edge for this element, specifies the sub-summarize edge.
	 */
	private final Pair<STATE, Boolean> mDuplicatorChoice;
	/**
	 * Vertex that was used right before this search element.
	 */
	private final Vertex<LETTER, STATE> mHistory;
	/**
	 * The origin vertex of this element.
	 */
	private final Vertex<LETTER, STATE> mOrigin;
	/**
	 * Summarize edge this element corresponds to.
	 */
	private final SummarizeEdge<LETTER, STATE> mSummarizeEdge;
	/**
	 * The target vertex of this element.
	 */
	private final Vertex<LETTER, STATE> mTarget;
	/**
	 * The current vertex of this element.
	 */
	private final Vertex<LETTER, STATE> mVertex;

	/**
	 * Creates a new search element with the given elements.
	 * 
	 * @param vertex
	 *            The vertex this element represents
	 * @param target
	 *            The target vertex this element is searching
	 * @param history
	 *            The vertex that was used right before this element, <tt>null</tt> if there is no.
	 * @param summarizeEdge
	 *            The summarize edge this element belongs to
	 * @param duplicatorChoice
	 *            The choice Duplicator makes in the summarize edge, specifies the sub-summarize edge
	 * @param origin
	 *            The origin of this search element
	 */
	public SearchElement(final Vertex<LETTER, STATE> vertex, final Vertex<LETTER, STATE> target,
			final Vertex<LETTER, STATE> history, SummarizeEdge<LETTER, STATE> summarizeEdge,
			Pair<STATE, Boolean> duplicatorChoice, final Vertex<LETTER, STATE> origin) {
		mVertex = vertex;
		mTarget = target;
		mHistory = history;
		mSummarizeEdge = summarizeEdge;
		mDuplicatorChoice = duplicatorChoice;
		mOrigin = origin;
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
		if (mDuplicatorChoice == null) {
			if (other.mDuplicatorChoice != null) {
				return false;
			}
		} else if (!mDuplicatorChoice.equals(other.mDuplicatorChoice)) {
			return false;
		}
		if (mHistory == null) {
			if (other.mHistory != null) {
				return false;
			}
		} else if (!mHistory.equals(other.mHistory)) {
			return false;
		}
		if (mSummarizeEdge == null) {
			if (other.mSummarizeEdge != null) {
				return false;
			}
		} else if (!mSummarizeEdge.equals(other.mSummarizeEdge)) {
			return false;
		}
		if (mTarget == null) {
			if (other.mTarget != null) {
				return false;
			}
		} else if (!mTarget.equals(other.mTarget)) {
			return false;
		}
		if (mVertex == null) {
			if (other.mVertex != null) {
				return false;
			}
		} else if (!mVertex.equals(other.mVertex)) {
			return false;
		} else if (!mOrigin.equals(other.mOrigin)) {
			return false;
		}
		return true;
	}

	/**
	 * Gets the choice Duplicator take for this summarize edge.
	 * 
	 * @return The choice Duplicator take for this summarize edge
	 */
	public Pair<STATE, Boolean> getDuplicatorChoice() {
		return mDuplicatorChoice;
	}

	/**
	 * Gets the vertex that was used right before this search element.
	 * 
	 * @return The vertex that was used right before this search element.
	 */
	public Vertex<LETTER, STATE> getHistory() {
		return mHistory;
	}

	/**
	 * Gets the origin.
	 * 
	 * @return The origin
	 */
	public Vertex<LETTER, STATE> getOrigin() {
		return mOrigin;
	}

	/**
	 * Gets the summarize edge this element corresponds to.
	 * 
	 * @return The summarize edge this element corresponds to
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return mSummarizeEdge;
	}

	/**
	 * Gets the target.
	 * 
	 * @return The target
	 */
	public Vertex<LETTER, STATE> getTarget() {
		return mTarget;
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
		result = prime * result + ((mDuplicatorChoice == null) ? 0 : mDuplicatorChoice.hashCode());
		result = prime * result + ((mHistory == null) ? 0 : mHistory.hashCode());
		result = prime * result + ((mSummarizeEdge == null) ? 0 : mSummarizeEdge.hashCode());
		result = prime * result + ((mTarget == null) ? 0 : mTarget.hashCode());
		result = prime * result + ((mVertex == null) ? 0 : mVertex.hashCode());
		result = prime * result + ((mOrigin == null) ? 0 : mOrigin.hashCode());
		return result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		return "SearchElement [mDuplicatorChoice=" + mDuplicatorChoice + ", mHistory=" + mHistory + ", mSummarizeEdge="
				+ mSummarizeEdge + ", mTarget=" + mTarget + ", mVertex=" + mVertex + ", mOrigin=" + mOrigin + "]";
	}
}
