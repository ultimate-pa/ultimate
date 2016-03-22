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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.vertices;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

/**
 * A vertex representing that its <i>Spoiler</i>s turn in the game defined by a
 * {@link de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.AGameGraph
 * AGameGraph}.<br/>
 * <br/>
 * 
 * The vertex representation is <b>(q0, q1, bit)</b> which means <i>Spoiler</i>
 * is currently at state q0 and must make a move using an arbitrary transition
 * whereas <i>Duplicator</i> now is at q1 and later must respond to
 * <i>Spoiler</i>s decision. The bit encodes extra information if needed.
 * 
 * This object extends regular SpoilerVertices by giving it a set of down
 * states. Both, the left and right, states are interpreted as up states and can
 * have multiple down states. Thus a vertex represents a combination of double
 * decker states.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of nwa automaton
 * @param <STATE>
 *            State class of nwa automaton
 */
public final class SpoilerDoubleDeckerVertex<LETTER, STATE> extends SpoilerVertex<LETTER, STATE> {

	/**
	 * The summarize edge this vertex belongs to if it is generated as a shadow
	 * vertex, <tt>null</tt> if not set.
	 */
	private final SummarizeEdge<LETTER, STATE> m_SummarizeEdge;
	/**
	 * Internal set of all down state configurations of the vertex.
	 */
	private final HashSet<VertexDownState<STATE>> m_VertexDownStates;

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * The double decker information first is blank after construction.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 */
	public SpoilerDoubleDeckerVertex(final int priority, final boolean b, final STATE q0, final STATE q1) {
		this(priority, b, q0, q1, null);
	}

	/**
	 * Constructs a new spoiler vertex with given representation <b>(q0, q1,
	 * bit)</b> which means <i>Spoiler</i> is currently at state q0 and must
	 * make a move using an arbitrary transition whereas <i>Duplicator</i> now
	 * is at q1 and later must respond to <i>Spoiler</i>s decision. The bit
	 * encodes extra information if needed.
	 * 
	 * The double decker information first is blank after construction.
	 * 
	 * @param priority
	 *            The priority of the vertex
	 * @param b
	 *            The extra bit of the vertex
	 * @param q0
	 *            The state spoiler is at, interpreted as up state
	 * @param q1
	 *            The state duplicator is at, interpreted as up state
	 * @param summarizeEdge
	 *            The summarize edge this vertex belongs to if it is generated
	 *            as a shadow vertex.
	 */
	public SpoilerDoubleDeckerVertex(final int priority, final boolean b, final STATE q0, final STATE q1,
			final SummarizeEdge<LETTER, STATE> summarizeEdge) {
		super(priority, b, q0, q1);
		m_VertexDownStates = new HashSet<>();
		m_SummarizeEdge = summarizeEdge;
	}

	/**
	 * Adds a given vertex down state to the vertex if not already present.
	 * 
	 * @param vertexDownState
	 *            Configuration to add
	 * @return If the given configuration was added to the vertex, i.e. if it
	 *         was not already present.
	 */
	public boolean addVertexDownState(final VertexDownState<STATE> vertexDownState) {
		return m_VertexDownStates.add(vertexDownState);
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
		if (!super.equals(obj)) {
			return false;
		}
		if (!(obj instanceof SpoilerDoubleDeckerVertex)) {
			return false;
		}
		SpoilerDoubleDeckerVertex<?, ?> other = (SpoilerDoubleDeckerVertex<?, ?>) obj;
		if (m_SummarizeEdge == null) {
			if (other.m_SummarizeEdge != null) {
				return false;
			}
		} else if (!m_SummarizeEdge.equals(other.m_SummarizeEdge)) {
			return false;
		}
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.
	 * buchiReduction.vertices.Vertex#getName()
	 */
	@Override
	public String getName() {
		StringBuilder sb = new StringBuilder();
		sb.append(getQ0() + "," + getQ1());
		sb.append("{");
		boolean isFirstVertexDownState = true;
		for (VertexDownState<STATE> vertexDownState : m_VertexDownStates) {
			if (!isFirstVertexDownState) {
				sb.append(",");
			}
			sb.append(vertexDownState.toString());
			isFirstVertexDownState = false;
		}
		sb.append("}");
		return sb.toString();
	}

	/**
	 * Gets the summarize edge this vertex belongs to or <tt>null</tt> if not
	 * set.
	 * 
	 * @return The summarize edge this vertex belongs to or <tt>null</tt> if not
	 *         set.
	 */
	public SummarizeEdge<LETTER, STATE> getSummarizeEdge() {
		return m_SummarizeEdge;
	}

	/**
	 * Gets an unmodifiable set of all vertex down states of this vertex.
	 * 
	 * @return Returns an unmodifiable set of all vertex down states of this
	 *         vertex.
	 */
	public Set<VertexDownState<STATE>> getVertexDownStates() {
		return Collections.unmodifiableSet(m_VertexDownStates);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((m_SummarizeEdge == null) ? 0 : m_SummarizeEdge.hashCode());
		return result;
	}

	/**
	 * Returns if the vertex has a given vertex down state.
	 * 
	 * @param leftDownState
	 *            Left state of the down state configuration
	 * @param rightDownState
	 *            Right state of the down state configuration
	 * @return If the vertex has the given down state configuration
	 */
	public boolean hasVertexDownState(final STATE leftDownState, final STATE rightDownState) {
		return m_VertexDownStates.contains(new VertexDownState<STATE>(leftDownState, rightDownState));
	}

	/**
	 * Returns if the vertex has a given vertex down state.
	 * 
	 * @param vertexDownState
	 *            Down state configuration in ask
	 * @return If the vertex has the given down state configuration
	 */
	public boolean hasVertexDownState(final VertexDownState<STATE> vertexDownState) {
		return m_VertexDownStates.contains(vertexDownState);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder sb = new StringBuilder();
		sb.append("<").append(isB()).append(",(").append(getQ0()).append(",");
		sb.append(getQ1());

		sb.append("{");
		boolean isFirstVertexDownState = true;
		for (VertexDownState<STATE> vertexDownState : m_VertexDownStates) {
			if (!isFirstVertexDownState) {
				sb.append(",");
			}
			sb.append(vertexDownState.toString());
			isFirstVertexDownState = false;
		}
		sb.append("}");

		sb.append("),p:").append(getPriority()).append(",pm:").append(pm);
		sb.append(">");
		return sb.toString();
	}
}
