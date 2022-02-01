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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance;

import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;

import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.StatisticsType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;

/**
 * Class that is used by {@link ASimulation} to measure its performance. Has timer and counter to save performance data.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class SimulationPerformance {

	/**
	 * Value for a non valid counting result.
	 */
	public static final int NO_COUNTING_RESULT = -1;
	/**
	 * Value for a non valid time result.
	 */
	public static final long NO_TIME_RESULT = -1;

	/**
	 * Holds all counting measures that are monitored.
	 */
	private final LinkedHashMap<CountingMeasure, Integer> mCountingMeasures;

	/**
	 * If the simulation uses SCC optimization or not.
	 */
	private final boolean mIsUsingSccs;
	/**
	 * Name for the performance object to distinguish it from others.
	 */
	private String mName;
	/**
	 * If the performance object represents a simulation that has thrown an out of memory error.
	 */
	private boolean mOutOfMemory;
	/**
	 * The type of the simulation that is monitored.
	 */
	private final SimulationOrMinimizationType mSimType;
	/**
	 * If the performance object represents a simulation that has timed out.
	 */
	private boolean mTimedOut;
	/**
	 * Holds all time measures that are monitored.
	 */
	private final LinkedHashMap<TimeMeasure, List<Long>> mTimeMeasures;

	/**
	 * Holds all starting timestamps for monitored time measures.
	 */
	private final LinkedHashMap<TimeMeasure, Long> mTimeMeasureStartTimes;

	/**
	 * Creates a simulation performance object that monitors the performance of a given simulation.
	 * 
	 * @param simType
	 *            Type of the simulation
	 * @param isUsingSccs
	 *            If the simulation uses a SCC optimization
	 */
	public SimulationPerformance(final SimulationOrMinimizationType simType, final boolean isUsingSccs) {
		mSimType = simType;
		mTimeMeasures = new LinkedHashMap<>();
		mTimeMeasureStartTimes = new LinkedHashMap<>();
		mCountingMeasures = new LinkedHashMap<>();
		mIsUsingSccs = isUsingSccs;
		mTimedOut = false;
		mOutOfMemory = false;
		mName = "";
	}

	/**
	 * Converts a given counting measure type to its equivalent statistics type.
	 * 
	 * @param countingMeasure
	 *            Time measure to convert
	 * @return The equivalent statistics type object
	 */
	public static StatisticsType convertCountingMeasureToStatistic(final CountingMeasure countingMeasure) {
		if (countingMeasure.equals(CountingMeasure.BUCHI_STATES)) {
			return StatisticsType.STATES_INPUT;
		} else if (countingMeasure.equals(CountingMeasure.RESULT_STATES)) {
			return StatisticsType.STATES_OUTPUT;
		} else if (countingMeasure.equals(CountingMeasure.REMOVED_STATES)) {
			return StatisticsType.STATES_REDUCTION_ABSOLUTE;
		}

		// Try to find a type with an equal name
		return StatisticsType.valueOf(countingMeasure.name());
	}

	/**
	 * Converts a given time measure type to its equivalent statistics type.
	 * 
	 * @param timeMeasure
	 *            Time measure to convert
	 * @return The equivalent statistics type object
	 */
	public static StatisticsType convertTimeMeasureToStatistic(final TimeMeasure timeMeasure) {
		if (timeMeasure.equals(TimeMeasure.OVERALL)) {
			return StatisticsType.TIME_SIMULATION_OLD;
		}

		// Try to find a type with an equal name
		return StatisticsType.valueOf(timeMeasure.name());
	}

	/**
	 * Creates an empty simulation performance object that is out of memory.
	 * 
	 * @param type
	 *            Type of the simulation
	 * @param useSccs
	 *            If the simulation usesSCCs
	 * @return The out of memory simulation performance object
	 */
	public static SimulationPerformance createOutOfMemoryPerformance(final SimulationOrMinimizationType type,
			final boolean useSccs) {
		final SimulationPerformance performance = new SimulationPerformance(type, useSccs);
		performance.outOfMemory();
		return performance;
	}

	/**
	 * Creates an empty simulation performance object that has timed out.
	 * 
	 * @param type
	 *            Type of the simulation
	 * @param useSccs
	 *            If the simulation usesSCCs
	 * @return The timed out simulation performance object
	 */
	public static SimulationPerformance createTimedOutPerformance(final SimulationOrMinimizationType type,
			final boolean useSccs) {
		final SimulationPerformance performance = new SimulationPerformance(type, useSccs);
		performance.timeOut();
		return performance;
	}

	/**
	 * Adds all counting and time measures of the other object to this given object. Counting measures will get merged
	 * additive.
	 * 
	 * @param other
	 *            Simulation object to add measures from
	 */
	public void addAllMeasures(final SimulationPerformance other) {
		final LinkedHashMap<CountingMeasure, Integer> countingMeasuresToAdd = other.getCountingMeasures();
		final LinkedHashMap<TimeMeasure, List<Long>> timeMeasuresToAdd = other.getTimeMeasures();

		for (final Entry<TimeMeasure, List<Long>> timeMeasure : timeMeasuresToAdd.entrySet()) {
			for (final Long duration : timeMeasure.getValue()) {
				addTimeMeasureValue(timeMeasure.getKey(), duration);
			}
		}
		for (final Entry<CountingMeasure, Integer> countingMeasure : countingMeasuresToAdd.entrySet()) {
			final int current = getCountingMeasureResult(countingMeasure.getKey());
			int valueToSet = current;
			if (current != NO_COUNTING_RESULT) {
				valueToSet += countingMeasure.getValue();
			} else {
				valueToSet = countingMeasure.getValue();
			}
			if (valueToSet != NO_COUNTING_RESULT && valueToSet != current) {
				setCountingMeasure(countingMeasure.getKey(), valueToSet);
			}
		}
	}

	/**
	 * Adds a given value to the duration list of a given time measure.
	 * 
	 * @param type
	 *            Type of the time measure
	 * @param duration
	 *            Duration to add
	 */
	public void addTimeMeasureValue(final TimeMeasure type, final long duration) {
		if (!mTimeMeasures.containsKey(type)) {
			mTimeMeasures.put(type, new LinkedList<>());
		}
		mTimeMeasures.get(type).add(duration);
	}

	/**
	 * Exports this simulation performance object to an AutomataOperationStatistics object.
	 * 
	 * @return An AutomataOperationStatistics object holding the equivalent data than this object
	 */
	public AutomataOperationStatistics exportToAutomataOperationStatistics() {
		final AutomataOperationStatistics stats = new AutomataOperationStatistics();
		exportToExistingAutomataOperationStatistics(stats);
		return stats;
	}

	/**
	 * Exports this simulation performance object to an AutomataOperationStatistics object.
	 * 
	 * @param stats
	 *            existing statistics object to add data to
	 */
	public void exportToExistingAutomataOperationStatistics(final AutomataOperationStatistics stats) {
		// Meta data
//		stats.addKeyValuePair(StatisticsType.OPERATION_NAME, getSimType());
//		stats.addKeyValuePair(StatisticsType.ATS_ID, getName());
		stats.addKeyValuePair(StatisticsType.HAS_TIMED_OUT, hasTimedOut());
		stats.addKeyValuePair(StatisticsType.IS_OUT_OF_MEMORY, isOutOfMemory());
		stats.addKeyValuePair(StatisticsType.IS_USING_SCCS, isUsingSccs());

		// Time measures
		for (final TimeMeasure measure : getTimeMeasures().keySet()) {
			final long value = getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);
			if (value != NO_TIME_RESULT) {
				stats.addKeyValuePair(convertTimeMeasureToStatistic(measure), value);
			}
		}

		// Counting measures
		// Christian 2017-03-25 I commented this out because it overwrites existing statistics from the superclass.
//		for (final CountingMeasure measure : getCountingMeasures().keySet()) {
//			final int value = getCountingMeasureResult(measure);
//			if (value != NO_COUNTING_RESULT) {
//				stats.addKeyValuePair(convertCountingMeasureToStatistic(measure), value);
//			}
//		}
	}

	/**
	 * Gets the result for a given counting measure if known or {@link #NO_COUNTING_RESULT}.
	 * 
	 * @param type
	 *            Type of the counting measure to get
	 * @return The result for a given counting measure if known or {@link #NO_COUNTING_RESULT}.
	 */
	public int getCountingMeasureResult(final CountingMeasure type) {
		if (!mCountingMeasures.containsKey(type)) {
			return NO_COUNTING_RESULT;
		}
		return mCountingMeasures.get(type);
	}

	/**
	 * Gets the counting measures.
	 * 
	 * @return The counting measures.
	 */
	public LinkedHashMap<CountingMeasure, Integer> getCountingMeasures() {
		return mCountingMeasures;
	}

	/**
	 * Returns the name of the performance object.
	 * 
	 * @return The name of the object.
	 */
	public String getName() {
		return mName;
	}

	/**
	 * Gets the type of the simulation monitored.
	 * 
	 * @return The type of the simulation monitored.
	 */
	public SimulationOrMinimizationType getSimType() {
		return mSimType;
	}

	/**
	 * Gets the result for a given time measure if known or {@link #NO_TIME_RESULT}. If there are multiple stored values
	 * for this measure they can be handled using a given {@link MultipleDataOption}.
	 * 
	 * @param type
	 *            Type of the time measure to get
	 * @param option
	 *            Option how multiple data values should be handled.
	 * @return The time measure result to get
	 */
	public long getTimeMeasureResult(final TimeMeasure type, final MultipleDataOption option) {
		final List<Long> measureList = mTimeMeasures.get(type);
		if (measureList == null || measureList.isEmpty()) {
			return NO_TIME_RESULT;
		}

		long timeResult = 0;
		for (final long timeMeasure : measureList) {
			if (timeMeasure == NO_TIME_RESULT) {
				continue;
			}
			if (option.equals(MultipleDataOption.ADDITIVE) || option.equals(MultipleDataOption.AVERAGE)) {
				timeResult += timeMeasure;
			} else if (option.equals(MultipleDataOption.MAXIMUM)) {
				if (timeMeasure > timeResult) {
					timeResult = timeMeasure;
				}
			} else if (option.equals(MultipleDataOption.MINIMIUM)) {
				if (timeMeasure < timeResult) {
					timeResult = timeMeasure;
				}
			}
		}
		if (option.equals(MultipleDataOption.AVERAGE)) {
			timeResult = Math.round((timeResult + 0.0) / measureList.size());
		}

		if (timeResult <= 0) {
			return NO_TIME_RESULT;
		}
		return timeResult;
	}

	/**
	 * Gets all results of a given time measure.
	 * 
	 * @param type
	 *            Type of the time measures to get
	 * @return All results of a given time measure.
	 */
	public List<Long> getTimeMeasureResults(final TimeMeasure type) {
		return mTimeMeasures.get(type);
	}

	/**
	 * Gets the time measures.
	 * 
	 * @return The time measures.
	 */
	public LinkedHashMap<TimeMeasure, List<Long>> getTimeMeasures() {
		return mTimeMeasures;
	}

	/**
	 * Returns whether the performance object represents a simulation that has timed out.
	 * 
	 * @return Whether the performance object represents a simulation that has timed out.
	 */
	public boolean hasTimedOut() {
		return mTimedOut;
	}

	/**
	 * Increases the stored counter of a given counting measure or sets it to 1 if it was not stored.
	 * 
	 * @param type
	 *            Type of the counting measure to increase
	 */
	public void increaseCountingMeasure(final CountingMeasure type) {
		if (!mCountingMeasures.containsKey(type)) {
			mCountingMeasures.put(type, 1);
		} else {
			final int counter = mCountingMeasures.get(type);
			mCountingMeasures.put(type, counter + 1);
		}
	}

	/**
	 * Returns whether the performance object represents a simulation that has thrown an out of memory error.
	 * 
	 * @return Whether the performance object represents a simulation that has throen an out of memory error.
	 */
	public boolean isOutOfMemory() {
		return mOutOfMemory;
	}

	/**
	 * If the monitored simulation uses a SCC simulation.
	 * 
	 * @return If the monitored simulation uses a SCC simulation.
	 */
	public boolean isUsingSccs() {
		return mIsUsingSccs;
	}

	/**
	 * If called the performance object indicates that the represented simulation has thrown an out of memory error.
	 */
	public void outOfMemory() {
		mOutOfMemory = true;
	}

	/**
	 * Sets the value for a given counting measure if it is not zero.
	 * 
	 * @param type
	 *            Type of the counting measure to set
	 * @param counter
	 *            Value to set which must not be zero
	 */
	public void setCountingMeasure(final CountingMeasure type, final int counter) {
		if (counter != 0) {
			mCountingMeasures.put(type, counter);
		}
	}

	/**
	 * Sets the name of the performance object.
	 * 
	 * @param name
	 *            The name to set
	 */
	public void setName(final String name) {
		mName = name;
	}

	/**
	 * Starts the timer for a given time measure.
	 * 
	 * @param type
	 *            Type of the time measure to start
	 */
	public void startTimeMeasure(final TimeMeasure type) {
		final long startTime = System.currentTimeMillis();
		mTimeMeasureStartTimes.put(type, startTime);
	}

	/**
	 * Stops and saves the timer for a given time measure and returns the duration of the measure.
	 * 
	 * @param type
	 *            Type of the time measure to stop
	 * @return The duration of the measure.
	 */
	public long stopTimeMeasure(final TimeMeasure type) {
		final long endTime = System.currentTimeMillis();
		long startTime = mTimeMeasureStartTimes.get(type);
		if (!mTimeMeasureStartTimes.containsKey(type)) {
			startTime = 0;
		}
		final long duration = endTime - startTime;
		saveTimeMeasureResult(type, duration);
		return duration;
	}

	/**
	 * If called the performance object indicates that the represented simulation timed out.
	 */
	public void timeOut() {
		mTimedOut = true;
	}

	/**
	 * Saves a given duration for a given time measure.
	 * 
	 * @param type
	 *            Type of the time measure to save
	 * @param duration
	 *            Duration to save
	 */
	private void saveTimeMeasureResult(final TimeMeasure type, final long duration) {
		List<Long> measureList = mTimeMeasures.get(type);
		if (measureList == null) {
			measureList = new LinkedList<>();
			mTimeMeasures.put(type, measureList);
		}
		measureList.add(duration);
	}
}
