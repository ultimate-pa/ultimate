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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.Vertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.simulation.util.VertexValueContainer;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Class that stores information of changes made to a {@link AGameGraph}.<br/>
 * <br/>
 * 
 * It can remember changed edges, vertices and values of vertices.<br/>
 * A GameGraphChanges object can then be used to undo made changes for a game
 * graph by using {@link AGameGraph#undoChanges(GameGraphChanges)}.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class GameGraphChanges<LETTER, STATE> {

	/**
	 * Stores information about changed edges.<br/>
	 * Stored as (source, destination, type of change).
	 */
	private final NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> m_ChangedEdges;

	/**
	 * Stores information about changed vertices.<br/>
	 * Stored as (vertex, type of changes).
	 */
	private final HashMap<Vertex<LETTER, STATE>, EGameGraphChangeType> m_ChangedVertices;

	/**
	 * Stores information about remembered values of vertices.<br/>
	 * Stored as (vertex, value container).
	 */
	private final HashMap<Vertex<LETTER, STATE>, VertexValueContainer> m_RememberedValues;

	/**
	 * Stores information about vertices that are either source or destination
	 * of an changed edges.
	 */
	private final HashSet<Vertex<LETTER, STATE>> m_VerticesInvolvedInEdgeChanges;

	/**
	 * Creates a new game graph changes object with no changes at default.
	 */
	public GameGraphChanges() {
		m_ChangedEdges = new NestedMap2<>();
		m_VerticesInvolvedInEdgeChanges = new HashSet<>();
		m_ChangedVertices = new HashMap<>();
		m_RememberedValues = new HashMap<>();
	}

	/**
	 * Stores information about an added edge.<br/>
	 * Nullifies changes if the given edge was removed before.
	 * 
	 * @param src
	 *            Source of the added edge
	 * @param dest
	 *            Destination of the added edge
	 */
	public void addedEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		changedEdge(src, dest, EGameGraphChangeType.ADDITION);
	}

	/**
	 * Stores information about an added vertex.<br/>
	 * Nullifies changes if the given vertex was removed before.
	 * 
	 * @param vertex
	 *            Vertex that was added
	 */
	public void addedVertex(final Vertex<LETTER, STATE> vertex) {
		changedVertex(vertex, EGameGraphChangeType.ADDITION);
	}

	/**
	 * Gets the information about changed edges.<br/>
	 * Stored as (source, destination, type of change).
	 * 
	 * @return The information about changed edges
	 */
	public NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> getChangedEdges() {
		return m_ChangedEdges;
	}

	/**
	 * Gets the information about changed vertices.<br/>
	 * Stored as (vertex, type of change).
	 * 
	 * @return The information about changed vertices
	 */
	public HashMap<Vertex<LETTER, STATE>, EGameGraphChangeType> getChangedVertices() {
		return m_ChangedVertices;
	}

	/**
	 * Gets the information about remembered values.<br/>
	 * Stored as (vertex, value container).
	 * 
	 * @return The information about remembered values
	 */
	public HashMap<Vertex<LETTER, STATE>, VertexValueContainer> getRememberedVertexValues() {
		return m_RememberedValues;
	}

	/**
	 * Returns if the given vertex has a remembered entry for the <i>BEff
	 * value</i> stored.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return True if there is a remembered entry for the <i>BEff value</i>
	 *         stored, false if not.
	 */
	public boolean hasBEffEntry(final Vertex<LETTER, STATE> vertex) {
		return m_RememberedValues.get(vertex) != null
				&& VertexValueContainer.isValueValid(m_RememberedValues.get(vertex).getBestNeighborMeasure());
	}

	/**
	 * Returns if the given vertex has a remembered entry for the <i>C value</i>
	 * stored.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return True if there is a remembered entry for the <i>C value</i>
	 *         stored, false if not.
	 */
	public boolean hasCEntry(final Vertex<LETTER, STATE> vertex) {
		return m_RememberedValues.get(vertex) != null
				&& VertexValueContainer.isValueValid(m_RememberedValues.get(vertex).getNeighborCounter());
	}

	/**
	 * Returns if the given vertex has a remembered entry for the <i>Progress
	 * measure value</i> stored.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return True if there is a remembered entry for the <i>Progress measure
	 *         value</i> stored, false if not.
	 */
	public boolean hasPmEntry(final Vertex<LETTER, STATE> vertex) {
		return m_RememberedValues.get(vertex) != null
				&& VertexValueContainer.isValueValid(m_RememberedValues.get(vertex).getProgressMeasure());
	}

	/**
	 * Returns if the given vertex has an <i>vertex addition</i> entry stored.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @return True if the given vertex has an <i>vertex addition</i> entry
	 *         stored, false if not
	 */
	public boolean isAddedVertex(final Vertex<LETTER, STATE> vertex) {
		EGameGraphChangeType type = m_ChangedVertices.get(vertex);
		return type != null && type.equals(EGameGraphChangeType.ADDITION);
	}

	/**
	 * Returns if the given vertex is either the source or destination of an
	 * edge that has a <i>change entry</i> stored.
	 * 
	 * @param vertex
	 *            Vertex of interest
	 * @return True if the given vertex is either the source or destination of
	 *         an edge that has a <i>change entry</i> stored, false if not.
	 */
	public boolean isVertexInvolvedInEdgeChanges(final Vertex<LETTER, STATE> vertex) {
		return m_VerticesInvolvedInEdgeChanges.contains(vertex);
	}

	/**
	 * Merges the given {@link GameGraphChanges} object with this object by
	 * adding all information of the second to the first.<br/>
	 * If the second has stored an addition whereas the first has a removal the
	 * resulting change gets nullified and vice versa.<br/>
	 * The given boolean argument gives the option to keep the remembered value
	 * of this object if the second also has a remembered value. This can be
	 * used to always keep the oldest entry or the newest.
	 * 
	 * @param changes
	 *            Change object to merge with
	 * @param rememberValuesOfFirst
	 *            True if the remembered values of this object should be kept if
	 *            the second also has an entry, false if not.
	 */
	public void merge(final GameGraphChanges<LETTER, STATE> changes, final boolean rememberValuesOfFirst) {
		if (changes == null) {
			return;
		}

		// Merge changed edges
		NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedEdges = changes
				.getChangedEdges();
		for (Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> changedEdge : changedEdges
				.entrySet()) {
			Vertex<LETTER, STATE> src = changedEdge.getFirst();
			Vertex<LETTER, STATE> dest = changedEdge.getSecond();
			EGameGraphChangeType type = changedEdge.getThird();

			Map<Vertex<LETTER, STATE>, EGameGraphChangeType> changedMap = m_ChangedEdges.get(src);
			EGameGraphChangeType changeType = null;
			if (changedMap != null) {
				changeType = m_ChangedEdges.get(src).get(dest);
			}
			if (changeType == null || changeType.equals(EGameGraphChangeType.NO_CHANGE)) {
				// Only add edge change if unknown until now
				m_ChangedEdges.put(src, dest, type);
			} else if ((changeType == EGameGraphChangeType.ADDITION && type == EGameGraphChangeType.REMOVAL)
					|| (changeType == EGameGraphChangeType.REMOVAL && type == EGameGraphChangeType.ADDITION)) {
				// Nullify change if it was added and then
				// removed or vice versa
				m_ChangedEdges.remove(src, dest);
			}
			m_VerticesInvolvedInEdgeChanges.add(src);
			m_VerticesInvolvedInEdgeChanges.add(dest);
		}

		// Merge changed vertices
		HashMap<Vertex<LETTER, STATE>, EGameGraphChangeType> changedVertices = changes.getChangedVertices();
		for (Entry<Vertex<LETTER, STATE>, EGameGraphChangeType> changedVertix : changedVertices.entrySet()) {
			EGameGraphChangeType changeType = m_ChangedVertices.get(changedVertix.getKey());
			if (changeType == null || changeType.equals(EGameGraphChangeType.NO_CHANGE)) {
				// Only add vertex change if unknown until now
				m_ChangedVertices.put(changedVertix.getKey(), changedVertix.getValue());
			} else if ((changeType == EGameGraphChangeType.ADDITION
					&& changedVertix.getValue() == EGameGraphChangeType.REMOVAL)
					|| (changeType == EGameGraphChangeType.REMOVAL
							&& changedVertix.getValue() == EGameGraphChangeType.ADDITION)) {
				// Nullify change if it was added and then
				// removed or vice versa
				m_ChangedVertices.remove(changedVertix.getKey());
			}
		}

		// Update the remembered values
		HashMap<Vertex<LETTER, STATE>, VertexValueContainer> rememberedValues = changes.getRememberedVertexValues();
		for (Entry<Vertex<LETTER, STATE>, VertexValueContainer> valuesEntry : rememberedValues.entrySet()) {
			Vertex<LETTER, STATE> vertex = valuesEntry.getKey();
			VertexValueContainer values = valuesEntry.getValue();

			ensureVertexValueContainerIsInitiated(vertex);
			VertexValueContainer currentValues = m_RememberedValues.get(vertex);

			/*
			 * Only update if new value is valid and user wishes to remember the
			 * newer value or if he wish to remember the old value but the old
			 * is not valid.
			 */
			// Update ProgressMeasure
			if (VertexValueContainer.isValueValid(values.getProgressMeasure())) {
				if (!rememberValuesOfFirst || !VertexValueContainer.isValueValid(currentValues.getProgressMeasure())) {
					currentValues.setProgressMeasure(values.getProgressMeasure());
				}
			}
			// Update BestNeighborMeasure
			if (VertexValueContainer.isValueValid(values.getBestNeighborMeasure())) {
				if (!rememberValuesOfFirst
						|| !VertexValueContainer.isValueValid(currentValues.getBestNeighborMeasure())) {
					currentValues.setBestNeighborMeasure(values.getBestNeighborMeasure());
				}
			}
			// Update NeighborCounter
			if (VertexValueContainer.isValueValid(values.getNeighborCounter())) {
				if (!rememberValuesOfFirst || !VertexValueContainer.isValueValid(currentValues.getNeighborCounter())) {
					currentValues.setNeighborCounter(values.getNeighborCounter());
				}
			}
		}
	}

	/**
	 * Stores information about the <i>BEff value</i> of a given vertex.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @param value
	 *            The value to remember
	 */
	public void rememberBEffVertex(final Vertex<LETTER, STATE> vertex, final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setBestNeighborMeasure(value);
	}

	/**
	 * Stores information about the <i>C value</i> of a given vertex.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @param value
	 *            The value to remember
	 */
	public void rememberCVertex(final Vertex<LETTER, STATE> vertex, final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setNeighborCounter(value);
	}

	/**
	 * Stores information about the <i>Progress measure value</i> of a given
	 * vertex.
	 * 
	 * @param vertex
	 *            The vertex of interest
	 * @param value
	 *            The value to remember
	 */
	public void rememberPmVertex(final Vertex<LETTER, STATE> vertex, final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setProgressMeasure(value);
	}

	/**
	 * Stores information about a removed edge.<br/>
	 * Nullifies changes if the given edge was added before.
	 * 
	 * @param src
	 *            Source of the removed edge
	 * @param dest
	 *            Destination of the removed edge
	 */
	public void removedEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest) {
		changedEdge(src, dest, EGameGraphChangeType.REMOVAL);
	}

	/**
	 * Stores information about a removed vertex.<br/>
	 * Nullifies changes if the given vertex was added before.
	 * 
	 * @param vertex
	 *            Vertex that was removed
	 */
	public void removedVertex(final Vertex<LETTER, STATE> vertex) {
		changedVertex(vertex, EGameGraphChangeType.REMOVAL);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("GameGraphChanges ggc = (");

		// Vertices
		result.append(lineSeparator + "\tchangedVertices = {");
		for (Entry<Vertex<LETTER, STATE>, EGameGraphChangeType> vertex : getChangedVertices().entrySet()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getKey().getQ0() + ", " + vertex.getKey().getQ1() + "), p:"
					+ vertex.getKey().getPriority() + ">\t" + vertex.getValue());
		}
		result.append(lineSeparator + "\t},");

		// Edges
		result.append(lineSeparator + "\tchangedEdges = {");
		for (Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>, EGameGraphChangeType> vertex : getChangedEdges()
				.entrySet()) {
			result.append(lineSeparator + "\t\t(" + vertex.getFirst().getQ0() + ", " + vertex.getFirst().getQ1());
			if (vertex.getFirst() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertex
						.getFirst();
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append(")\t--> (" + vertex.getSecond().getQ0() + ", " + vertex.getSecond().getQ1());
			if (vertex.getSecond() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertex
						.getSecond();
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append(")\t" + vertex.getThird());
		}
		result.append(lineSeparator + "\t}");

		// Remembered values
		result.append(lineSeparator + "\trememberedValues = {");
		for (Entry<Vertex<LETTER, STATE>, VertexValueContainer> vertexContainer : getRememberedVertexValues()
				.entrySet()) {
			result.append(lineSeparator + "\t\t(" + vertexContainer.getKey().getQ0() + ", "
					+ vertexContainer.getKey().getQ1());
			if (vertexContainer.getKey() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex = (DuplicatorVertex<LETTER, STATE>) vertexContainer
						.getKey();
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append(")\tPM:");
			result.append(vertexContainer.getValue().getProgressMeasure() + ", BNM:");
			result.append(vertexContainer.getValue().getBestNeighborMeasure() + ", NC:");
			result.append(vertexContainer.getValue().getNeighborCounter());
		}
		result.append(lineSeparator + "\t}");

		// Footer
		result.append(lineSeparator + ");");

		return result.toString();
	}

	/**
	 * Stores information about a changed edge.<br/>
	 * Nullifies changes if the given edge was added before if it was now
	 * removed or vice versa.
	 * 
	 * @param src
	 *            Source of the changed edge
	 * @param dest
	 *            Destination of the changed edge
	 * @param type
	 *            Type of the change
	 */
	private void changedEdge(final Vertex<LETTER, STATE> src, final Vertex<LETTER, STATE> dest,
			final EGameGraphChangeType type) {
		EGameGraphChangeType previousType = m_ChangedEdges.get(src, dest);
		// Nullify change if previously added and then removed or vice versa
		if (previousType != null && ((previousType.equals(EGameGraphChangeType.ADDITION)
				&& type.equals(EGameGraphChangeType.REMOVAL))
				|| (previousType.equals(EGameGraphChangeType.REMOVAL) && type.equals(EGameGraphChangeType.ADDITION)))) {
			m_ChangedEdges.remove(src, dest);
		} else {
			m_ChangedEdges.put(src, dest, type);
		}
		m_VerticesInvolvedInEdgeChanges.add(src);
		m_VerticesInvolvedInEdgeChanges.add(dest);
	}

	/**
	 * Stores information about a changed vertex.<br/>
	 * Nullifies changes if the given vertex was added before if it was now
	 * removed or vice versa.
	 * 
	 * @param vertex
	 *            Vertex that was changed
	 * @param type
	 *            Type of the change
	 */
	private void changedVertex(final Vertex<LETTER, STATE> vertex, final EGameGraphChangeType type) {
		EGameGraphChangeType previousType = m_ChangedVertices.get(vertex);
		// Nullify change if previously added and then removed or vice versa
		if (previousType != null && ((previousType.equals(EGameGraphChangeType.ADDITION)
				&& type.equals(EGameGraphChangeType.REMOVAL))
				|| (previousType.equals(EGameGraphChangeType.REMOVAL) && type.equals(EGameGraphChangeType.ADDITION)))) {
			m_ChangedVertices.remove(vertex);
		} else {
			m_ChangedVertices.put(vertex, type);
		}
	}

	/**
	 * Ensures the given vertex has a value container stored by creating a new
	 * empty container if there is no.<br/>
	 * This is used to prevent NPE at access.
	 * 
	 * @param key
	 *            Vertex to ensure the container for
	 */
	private void ensureVertexValueContainerIsInitiated(final Vertex<LETTER, STATE> key) {
		if (m_RememberedValues.get(key) == null) {
			m_RememberedValues.put(key, new VertexValueContainer());
		}
	}
}
