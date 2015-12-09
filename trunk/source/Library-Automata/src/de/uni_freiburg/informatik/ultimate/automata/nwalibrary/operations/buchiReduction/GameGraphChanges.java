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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction;

import java.util.HashMap;
import java.util.Map;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.DuplicatorVertex;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices.Vertex;
import de.uni_freiburg.informatik.ultimate.util.relation.NestedMap2;
import de.uni_freiburg.informatik.ultimate.util.relation.Triple;

/**
 * Doc comes later.
 * 
 * @author Daniel Tischner
 *
 * @param <LETTER>
 * @param <STATE>
 */
public class GameGraphChanges<LETTER, STATE> {
	
	private final NestedMap2<Vertex<LETTER, STATE>,
		Vertex<LETTER, STATE>, GameGraphChangeType> m_ChangedEdges;
	
	private final HashMap<Vertex<LETTER, STATE>,
		GameGraphChangeType> m_ChangedVertices;
	
	private final HashMap<Vertex<LETTER, STATE>,
		VertexValueContainer> m_RememberedValues;
	
	public GameGraphChanges() {
		m_ChangedEdges = new NestedMap2<Vertex<LETTER, STATE>,
				Vertex<LETTER, STATE>, GameGraphChangeType>();
		m_ChangedVertices = new HashMap<Vertex<LETTER, STATE>,
				GameGraphChangeType>();
		m_RememberedValues = new HashMap<Vertex<LETTER, STATE>,
				VertexValueContainer>();
	}
	
	public void addedEdge(final Vertex<LETTER, STATE> src,
			final Vertex<LETTER, STATE> dest) {
		changedEdge(src, dest, GameGraphChangeType.ADDITION);
	}
	
	public void addedVertex(final Vertex<LETTER, STATE> vertex) {
		changedVertex(vertex, GameGraphChangeType.ADDITION);
	}
	
	public NestedMap2<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>,
		GameGraphChangeType> getChangedEdges() {
		return m_ChangedEdges;
	}
	
	public HashMap<Vertex<LETTER, STATE>,
		GameGraphChangeType> getChangedVertices() {
		return m_ChangedVertices;
	}
	
	public HashMap<Vertex<LETTER, STATE>,
		VertexValueContainer> getRememberedVertexValues() {
		return m_RememberedValues;
	}
	
	public boolean isChangedEdgeSource(final Vertex<LETTER, STATE> vertex) {
		boolean isChangedEdgeSource = false;
		Map<Vertex<LETTER, STATE>, GameGraphChangeType> changedMap =
				m_ChangedEdges.get(vertex);
		if (changedMap != null) {
			for (GameGraphChangeType type : changedMap.values()) {
				if (type != GameGraphChangeType.NO_CHANGE) {
					isChangedEdgeSource = true;
					break;
				}
			}
		}
		return isChangedEdgeSource;
	}
	
	public boolean isAddedVertex(final Vertex<LETTER, STATE> vertex) {
		GameGraphChangeType type = m_ChangedVertices.get(vertex);
		return type != null && type.equals(GameGraphChangeType.ADDITION);
	}
	
	public boolean hasBEffEntry(final Vertex<LETTER, STATE> vertex) {
		return m_RememberedValues.get(vertex) != null
				&& m_RememberedValues.get(vertex).getBestNeighborMeasure()
				!= VertexValueContainer.NO_VALUE;
	}
	
	public boolean hasCEntry(final Vertex<LETTER, STATE> vertex) {
		return m_RememberedValues.get(vertex) != null
				&& m_RememberedValues.get(vertex).getNeighborCounter()
				!= VertexValueContainer.NO_VALUE;
	}
	
	public boolean hasPmEntry(final Vertex<LETTER, STATE> vertex) {
			return m_RememberedValues.get(vertex) != null
					&& m_RememberedValues.get(vertex).getProgressMeasure()
					!= VertexValueContainer.NO_VALUE;
	}
	
	public void merge(final GameGraphChanges<LETTER, STATE> changes,
			final boolean rememberValuesOfFirst) {
		if (changes == null) {
			return;
		}
		
		// Merge changed edges
		NestedMap2<Vertex<LETTER, STATE>,
			Vertex<LETTER, STATE>, GameGraphChangeType> changedEdges =
				changes.getChangedEdges();
		for (Triple<Vertex<LETTER, STATE>,
				Vertex<LETTER, STATE>, GameGraphChangeType> changedEdge :
					changedEdges.entrySet()) {
			Map<Vertex<LETTER, STATE>, GameGraphChangeType> changedMap =
					m_ChangedEdges.get(changedEdge.getFirst());
			GameGraphChangeType changeType = null;
			if (changedMap != null) {
				changeType = m_ChangedEdges.get(
						changedEdge.getFirst()).get(changedEdge.getSecond());
			}
			if (changeType == null
					|| changeType.equals(GameGraphChangeType.NO_CHANGE)) {
				// Only add edge change if unknown until now
				m_ChangedEdges.put(changedEdge.getFirst(),
						changedEdge.getSecond(), changedEdge.getThird());
			} else if ((changeType == GameGraphChangeType.ADDITION
					&& changedEdge.getThird() == GameGraphChangeType.REMOVAL)
					|| (changeType == GameGraphChangeType.REMOVAL
					&& changedEdge.getThird() == GameGraphChangeType.ADDITION)) {
				// Nullify change if it was added and then
				// removed or vice versa
				m_ChangedEdges.remove(changedEdge.getFirst(),
						changedEdge.getSecond());
			}
		}
		
		// Merge changed vertices
		HashMap<Vertex<LETTER, STATE>, GameGraphChangeType> changedVertices =
				changes.getChangedVertices();
		for (Entry<Vertex<LETTER, STATE>, GameGraphChangeType> changedVertix :
			changedVertices.entrySet()) {
			GameGraphChangeType changeType = m_ChangedVertices.get(
					changedVertix.getKey());
			if (changeType == null
					|| changeType.equals(GameGraphChangeType.NO_CHANGE)) {
				// Only add vertix change if unknown until now
				m_ChangedVertices.put(changedVertix.getKey(),
						changedVertix.getValue());
			} else if ((changeType == GameGraphChangeType.ADDITION
					&& changedVertix.getValue() == GameGraphChangeType.REMOVAL)
					|| (changeType == GameGraphChangeType.REMOVAL
					&& changedVertix.getValue() == GameGraphChangeType.ADDITION)) {
				// Nullify change if it was added and then
				// removed or vice versa
				m_ChangedVertices.remove(changedVertix.getKey());
			}
		}
		
		// Update the remembered values
		HashMap<Vertex<LETTER, STATE>, VertexValueContainer> rememberedValues =
				changes.getRememberedVertexValues();
		for (Entry<Vertex<LETTER, STATE>, VertexValueContainer> valuesEntry :
			rememberedValues.entrySet()) {
			Vertex<LETTER, STATE> vertex = valuesEntry.getKey();
			VertexValueContainer values = valuesEntry.getValue();
			
			ensureVertexValueContainerIsInitiated(vertex);
			VertexValueContainer currentValues = m_RememberedValues.get(vertex);
			
			/*
			 *  Only update if new value is not NO_VALUE and
			 *  user wishes to remember the newer value or
			 *  if he wish to remember the old value but
			 *  the old is NO_VALUE.
			 */
			// Update ProgressMeasure
			if (values.getProgressMeasure() != VertexValueContainer.NO_VALUE) {
				if (!rememberValuesOfFirst
						|| currentValues.getProgressMeasure()
						== VertexValueContainer.NO_VALUE) {
					currentValues.setProgressMeasure(values.getProgressMeasure());
				}
			}
			// Update BestNeighborMeasure
			if (values.getBestNeighborMeasure() != VertexValueContainer.NO_VALUE) {
				if (!rememberValuesOfFirst
						|| currentValues.getBestNeighborMeasure()
						== VertexValueContainer.NO_VALUE) {
					currentValues.setBestNeighborMeasure(
							values.getBestNeighborMeasure());
				}
			}
			// Update NeighborCounter
			if (values.getNeighborCounter() != VertexValueContainer.NO_VALUE) {
				if (!rememberValuesOfFirst
						|| currentValues.getNeighborCounter()
						== VertexValueContainer.NO_VALUE) {
					currentValues.setNeighborCounter(values.getNeighborCounter());
				}
			}
		}
	}
	
	public void rememberBEffVertex(final Vertex<LETTER, STATE> vertex,
			final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setBestNeighborMeasure(value);
	}
	
	public void rememberCVertex(final Vertex<LETTER, STATE> vertex,
			final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setNeighborCounter(value);
	}
	
	public void rememberPmVertex(final Vertex<LETTER, STATE> vertex,
			final int value) {
		ensureVertexValueContainerIsInitiated(vertex);
		m_RememberedValues.get(vertex).setProgressMeasure(value);
	}
	
	public void removedEdge(final Vertex<LETTER, STATE> src,
			final Vertex<LETTER, STATE> dest) {
		changedEdge(src, dest, GameGraphChangeType.REMOVAL);
	}
	
	public void removedVertex(final Vertex<LETTER, STATE> vertex) {
		changedVertex(vertex, GameGraphChangeType.REMOVAL);
	}
	
	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		String lineSeparator = System.lineSeparator();
		// Header
		result.append("GameGraphChanges ggc = (");
		
		// Vertices
		result.append(lineSeparator + "\tchangedVertices = {");
		for (Entry<Vertex<LETTER, STATE>, GameGraphChangeType> vertex : getChangedVertices().entrySet()) {
			result.append(lineSeparator + "\t\t<(" + vertex.getKey().getQ0()
				+ ", " + vertex.getKey().getQ1() + "), p:" + vertex.getKey().getPriority() + ">\t"
					+ vertex.getValue());
		}
		result.append(lineSeparator + "\t},");
		
		// Edges
		result.append(lineSeparator + "\tchangedEdges = {");
		for (Triple<Vertex<LETTER, STATE>, Vertex<LETTER, STATE>,
				GameGraphChangeType> vertex : getChangedEdges().entrySet()) {
			result.append(lineSeparator + "\t\t(" + vertex.getFirst().getQ0() + ", " + vertex.getFirst().getQ1());
			if (vertex.getFirst() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex =
						(DuplicatorVertex<LETTER, STATE>) vertex.getFirst();
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append(")\t--> (" + vertex.getSecond().getQ0() + ", " + vertex.getSecond().getQ1());
			if (vertex.getSecond() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex =
						(DuplicatorVertex<LETTER, STATE>) vertex.getSecond();
				result.append(", " + vertexAsDuplicatorVertex.getLetter());
			}
			result.append(")\t" + vertex.getThird());
		}
		result.append(lineSeparator + "\t}");
		
		// Remembered values
		result.append(lineSeparator + "\trememberedValues = {");
		for (Entry<Vertex<LETTER, STATE>, VertexValueContainer> vertexContainer :
			getRememberedVertexValues().entrySet()) {
			result.append(lineSeparator + "\t\t(" + vertexContainer.getKey().getQ0()
					+ ", " + vertexContainer.getKey().getQ1());
			if (vertexContainer.getKey() instanceof DuplicatorVertex) {
				DuplicatorVertex<LETTER, STATE> vertexAsDuplicatorVertex =
						(DuplicatorVertex<LETTER, STATE>) vertexContainer.getKey();
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
	
	private void changedEdge(final Vertex<LETTER, STATE> src,
			final Vertex<LETTER, STATE> dest, final GameGraphChangeType type) {
		GameGraphChangeType previousType = m_ChangedEdges.get(src, dest);
		// Nullify change if previously added and then removed or vice versa
		if (previousType != null
				&& ((previousType.equals(GameGraphChangeType.ADDITION)
							&& type.equals(GameGraphChangeType.REMOVAL))
						|| (previousType.equals(GameGraphChangeType.REMOVAL)
							&& type.equals(GameGraphChangeType.ADDITION)))) {
			m_ChangedEdges.remove(src, dest);
		} else {
			m_ChangedEdges.put(src, dest, type);
		}
	}
	
	private void changedVertex(final Vertex<LETTER, STATE> vertex,
			final GameGraphChangeType type) {
		GameGraphChangeType previousType = m_ChangedVertices.get(vertex);
		// Nullify change if previously added and then removed or vice versa
		if (previousType != null
				&& ((previousType.equals(GameGraphChangeType.ADDITION)
							&& type.equals(GameGraphChangeType.REMOVAL))
						|| (previousType.equals(GameGraphChangeType.REMOVAL)
							&& type.equals(GameGraphChangeType.ADDITION)))) {
			m_ChangedVertices.remove(vertex);
		} else {
			m_ChangedVertices.put(vertex, type);
		}
	}
	
	private void ensureVertexValueContainerIsInitiated(
			final Vertex<LETTER, STATE> key) {
		if (m_RememberedValues.get(key) == null) {
			m_RememberedValues.put(key, new VertexValueContainer());
		}
	}
}
