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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.vertices;

/**
 * Container for vertex values. Holds relevant
 * fields of {@link de.uni_freiburg.informatik.ultimate.automata.
 * nwalibrary.operations.buchiReduction.vertices.Vertex vertices}.
 * 
 * @author Daniel Tischner
 *
 */
public final class VertexValueContainer {

	/**
	 * Indicates that a field currently has no valid value.
	 */
	public static final int NO_VALUE = -1;

	/**
	 * The best neighbor measure.
	 */
	private int m_BestNeighborMeasure;

	/**
	 * The neighbor counter.
	 */
	private int m_NeighborCounter;

	/**
	 * The progress measure.
	 */
	private int m_ProgressMeasure;

	/**
	 * Creates a new vertex value container where all values are
	 * {@link #NO_VALUE}.
	 */
	public VertexValueContainer() {
		this(NO_VALUE, NO_VALUE, NO_VALUE);
	}

	/**
	 * Creates a new vertex value container with given values.
	 * 
	 * @param progressMeasure
	 *            The progress measure
	 * @param bestNeighborMeasure
	 *            The best neighbor measure
	 * @param neighborCounter
	 *            The neighbor counter
	 */
	public VertexValueContainer(int progressMeasure,
			int bestNeighborMeasure, int neighborCounter) {
		setProgressMeasure(progressMeasure);
		setBestNeighborMeasure(bestNeighborMeasure);
		setNeighborCounter(neighborCounter);
	}

	/**
	 * @return the bestNeighborMeasure
	 */
	public int getBestNeighborMeasure() {
		return m_BestNeighborMeasure;
	}

	/**
	 * @return the neighborCounter
	 */
	public int getNeighborCounter() {
		return m_NeighborCounter;
	}

	/**
	 * @return the progressMeasure
	 */
	public int getProgressMeasure() {
		return m_ProgressMeasure;
	}

	/**
	 * @param bestNeighborMeasure
	 *            the bestNeighborMeasure to set
	 */
	public void setBestNeighborMeasure(int bestNeighborMeasure) {
		this.m_BestNeighborMeasure = bestNeighborMeasure;
	}

	/**
	 * @param neighborCounter
	 *            the NeighborCounter to set
	 */
	public void setNeighborCounter(int neighborCounter) {
		this.m_NeighborCounter = neighborCounter;
	}

	/**
	 * @param progressMeasure
	 *            the progressMeasure to set
	 */
	public void setProgressMeasure(int progressMeasure) {
		this.m_ProgressMeasure = progressMeasure;
	}
}
