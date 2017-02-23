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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util;

/**
 * Container for vertex values. Holds relevant fields of
 * {@link de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.util.Vertex vertices}.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class VertexValueContainer {

	/**
	 * Indicates that a field currently has no valid value.
	 */
	private static final int NO_VALUE = -1;

	/**
	 * The best neighbor measure.
	 */
	private int mBestNeighborMeasure;

	/**
	 * The neighbor counter.
	 */
	private int mNeighborCounter;

	/**
	 * The progress measure.
	 */
	private int mProgressMeasure;

	/**
	 * Creates a new vertex value container where all values are
	 * {@link #NO_VALUE}.
	 */
	public VertexValueContainer() {
		mBestNeighborMeasure = NO_VALUE;
		mNeighborCounter = NO_VALUE;
		mProgressMeasure = NO_VALUE;
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
	public VertexValueContainer(final int progressMeasure, final int bestNeighborMeasure, final int neighborCounter) {
		setProgressMeasure(progressMeasure);
		setBestNeighborMeasure(bestNeighborMeasure);
		setNeighborCounter(neighborCounter);
	}

	/**
	 * Returns if the given value is valid or not.
	 * 
	 * @param value
	 *            The value of interest
	 * @return True if the value is valid, false if not
	 */
	public static boolean isValueValid(final int value) {
		return value != NO_VALUE;
	}

	/**
	 * Ensures that a given value is valid by comparing it to the internal field
	 * {@link #NO_VALUE}.
	 * 
	 * @param value
	 *            Value to ensure that it is valid
	 * @throws IllegalArgumentException
	 *             If the value is equals {@link #NO_VALUE}.
	 */
	private static void ensureValueIsValid(final int value) {
		if (!isValueValid(value)) {
			throw new IllegalArgumentException("Value must not be equals the internal value for 'NO_VALUE'.");
		}
	}

	/**
	 * @return the bestNeighborMeasure.
	 */
	public int getBestNeighborMeasure() {
		return mBestNeighborMeasure;
	}

	/**
	 * @return the neighborCounter.
	 */
	public int getNeighborCounter() {
		return mNeighborCounter;
	}

	/**
	 * @return the progressMeasure.
	 */
	public int getProgressMeasure() {
		return mProgressMeasure;
	}

	/**
	 * @param bestNeighborMeasure
	 *            the bestNeighborMeasure to set.
	 */
	public void setBestNeighborMeasure(final int bestNeighborMeasure) {
		ensureValueIsValid(bestNeighborMeasure);
		mBestNeighborMeasure = bestNeighborMeasure;
	}

	/**
	 * @param neighborCounter
	 *            the NeighborCounter to set.
	 */
	public void setNeighborCounter(final int neighborCounter) {
		ensureValueIsValid(neighborCounter);
		mNeighborCounter = neighborCounter;
	}

	/**
	 * @param progressMeasure
	 *            the progressMeasure to set.
	 */
	public void setProgressMeasure(final int progressMeasure) {
		ensureValueIsValid(progressMeasure);
		mProgressMeasure = progressMeasure;
	}
}
