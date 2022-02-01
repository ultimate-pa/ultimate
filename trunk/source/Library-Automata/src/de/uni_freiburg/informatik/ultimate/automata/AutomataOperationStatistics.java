/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata;

import java.util.ArrayList;
import java.util.List;
import java.util.Map.Entry;
import java.util.TreeMap;

import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.ICsvProviderProvider;
import de.uni_freiburg.informatik.ultimate.util.csv.SimpleCsvProvider;

/**
 * Object that stores statistics of an automata library operation.
 * <p>
 * Statistics are stored as a key-value map and are not allowed to be overwritten.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public class AutomataOperationStatistics implements ICsvProviderProvider<Object> {
	/**
	 * Used to indicate an invalid percentage (if the base is zero).
	 */
	private static final int INVALID_PERCENTAGE = -1;

	private final TreeMap<StatisticsType, Object> mKeyValueMap;

	/**
	 * Constructor.
	 */
	public AutomataOperationStatistics() {
		mKeyValueMap = new TreeMap<>();
	}

	@Override
	public ICsvProvider<Object> createCsvProvider() {
		final List<String> columnTitles = new ArrayList<>(mKeyValueMap.size());
		final List<Object> firstRow = new ArrayList<>(mKeyValueMap.size());
		for (final Entry<StatisticsType, Object> entry : mKeyValueMap.entrySet()) {
			columnTitles.add(entry.getKey().toString());
			firstRow.add(entry.getValue());
		}
		final SimpleCsvProvider<Object> result = new SimpleCsvProvider<>(columnTitles);
		result.addRow(firstRow);
		return result;
	}

	/**
	 * @param key
	 *            Key with which the specified value is to be associated.
	 * @param value
	 *            value to be associated with the specified key
	 */
	public void addKeyValuePair(final StatisticsType key, final Object value) {
		assert !mKeyValueMap.containsKey(key) : "The statistics for key " + key
				+ " would be overwritten, which is not allowed.";
		mKeyValueMap.put(key, value);
	}

	/**
	 * @param other
	 *            Statistics object whose entries are added.
	 */
	public void addAllStatistics(final AutomataOperationStatistics other) {
		for (final Entry<StatisticsType, Object> entry : other.mKeyValueMap.entrySet()) {
			addKeyValuePair(entry.getKey(), entry.getValue());
		}
	}

	/**
	 * Adds a key-value pair with the content being the percentage of the first key <tt>sndBaseKey</tt> wrt. the second
	 * key <tt>fstBaseKey</tt>.
	 * 
	 * @param fstBaseKey
	 *            first key
	 * @param sndBaseKey
	 *            second key
	 * @param resultKey
	 *            result key
	 */
	public void addPercentageData(final StatisticsType fstBaseKey, final StatisticsType sndBaseKey,
			final StatisticsType resultKey) {
		addPercentageDataHelper(fstBaseKey, sndBaseKey, resultKey, false);
	}

	/**
	 * Adds a key-value pair with the content being the percentage of the first key <tt>sndBaseKey</tt> wrt. the second
	 * key <tt>fstBaseKey</tt>.
	 * <p>
	 * The percentage is inverted, i.e., instead of <tt>x</tt> we add <tt>100 - x</tt>.
	 * 
	 * @param fstBaseKey
	 *            first key
	 * @param sndBaseKey
	 *            second key
	 * @param resultKey
	 *            result key
	 */
	public void addPercentageDataInverted(final StatisticsType fstBaseKey, final StatisticsType sndBaseKey,
			final StatisticsType resultKey) {
		addPercentageDataHelper(fstBaseKey, sndBaseKey, resultKey, true);
	}

	/**
	 * Adds a key-value pair with the content being the percentage of the first key <tt>sndBaseKey</tt> wrt. the second
	 * key <tt>fstBaseKey</tt>.
	 * 
	 * @param fstBaseKey
	 *            first key
	 * @param sndBaseKey
	 *            second key
	 * @param resultKey
	 *            result key
	 * @param invert
	 *            true iff percentage should be inverted, i.e., instead of <tt>x</tt> we add <tt>100 - x</tt>
	 */
	private void addPercentageDataHelper(final StatisticsType fstBaseKey, final StatisticsType sndBaseKey,
			final StatisticsType resultKey, final boolean invert) {
		final int fst = getInteger(fstBaseKey);
		if (fst == 0) {
			addKeyValuePair(resultKey, INVALID_PERCENTAGE);
			return;
		}
		final int snd = getInteger(sndBaseKey);
		final int percentageRaw = 100 * snd / fst;
		final Integer percentage = invert ? (100 - percentageRaw) : percentageRaw;
		addKeyValuePair(resultKey, percentage);
	}

	/**
	 * Adds a key-value pair with the content being the difference between the first key <tt>sndBaseKey</tt> wrt. the
	 * second key <tt>fstBaseKey</tt>.
	 * 
	 * @param fstBaseKey
	 *            first key
	 * @param sndBaseKey
	 *            second key
	 * @param resultKey
	 *            result key
	 */
	public void addDifferenceData(final StatisticsType fstBaseKey, final StatisticsType sndBaseKey,
			final StatisticsType resultKey) {
		final int difference = getDifference(fstBaseKey, sndBaseKey);
		addKeyValuePair(resultKey, difference);
	}

	private int getDifference(final StatisticsType fstBaseKey, final StatisticsType sndBaseKey) {
		final int fst = getInteger(fstBaseKey);
		final int snd = getInteger(sndBaseKey);
		return fst - snd;
	}

	private Integer getInteger(final StatisticsType key) {
		final Object raw = mKeyValueMap.get(key);
		if (raw == null) {
			throw new IllegalArgumentException("First insert the value for key " + key);
		}
		if (!(raw instanceof Integer)) {
			throw new IllegalArgumentException(key + " has a value stored that is not of integer type.");
		}
		return (Integer) raw;
	}

	@Override
	public String toString() {
		return mKeyValueMap.toString();
	}
}
