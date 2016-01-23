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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.performance;

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Utility class that offers methods which create comparison tables for
 * performance analyze.
 * 
 * @author Daniel Tischner
 *
 */
public final class ComparisonTables {

	/**
	 * Factor that, if multiplied with, converts seconds to milliseconds.
	 */
	public final static int SECONDS_TO_MILLIS = 1000;
	/**
	 * Decimal places to round duration of a method to.
	 */
	private final static int DECIMAL_PLACES = 3;
	/**
	 * Represents the value for full percentage.
	 */
	private final static int FULL_PERCENTAGE = 100;

	/**
	 * Creates a table that holds the full comparison data for each simulation
	 * type averaged over all automata instances respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createAveragedSimulationFullComparisonTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Process performance list into a sorted map structure
		LinkedHashMap<Pair<SimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = new LinkedHashMap<>();
		for (LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean simulationOfComparisonHasTimedOut = false;
			LinkedList<SimulationPerformance> performancesToAdd = new LinkedList<>();
			
			for (SimulationPerformance performanceOfSimulation : performanceComparison) {
				// Ignore comparison if a simulation has timed out
				if (performanceOfSimulation.hasTimedOut()) {
					simulationOfComparisonHasTimedOut = true;
					break;
				}
				
				performancesToAdd.add(performanceOfSimulation);
			}
			if (!simulationOfComparisonHasTimedOut) {
				// No timeout occurred, add performances
				for (SimulationPerformance performance : performancesToAdd) {
					SimulationType type = performance.getSimType();

					Pair<SimulationType, Boolean> simulationKey = new Pair<>(type, performance.isUsingSCCs());
					LinkedList<SimulationPerformance> performances = simulationToPerformances.get(simulationKey);
					if (performances == null) {
						performances = new LinkedList<>();
						simulationToPerformances.put(simulationKey, performances);
					}
					performances.add(performance);
				}
			}
		}

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS";
		SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		Set<TimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (TimeMeasure measure : timeMeasures) {
			header += separator + measure + "(&Oslash;)";
		}
		Set<CountingMeasure> countingMeasures = headerCandidate.getCountingMeasures().keySet();
		for (CountingMeasure measure : countingMeasures) {
			header += separator + measure + "(&Oslash;)";
		}
		table.add(header);

		// Rows of table
		for (Entry<Pair<SimulationType, Boolean>, LinkedList<SimulationPerformance>> entry : simulationToPerformances
				.entrySet()) {
			String row = entry.getKey().getFirst() + separator + entry.getKey().getSecond();

			for (TimeMeasure measure : timeMeasures) {
				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (SimulationPerformance performance : entry.getValue()) {
					long value = performance.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);
					if (value != SimulationPerformance.NO_TIME_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}
				long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				String valueAsString = "";
				if (averageOfValues == 0) {
					valueAsString = "&ndash;";
				} else {
					float valueInSeconds = millisToSeconds(averageOfValues);
					valueAsString = valueInSeconds + "";
				}

				row += separator + valueAsString;

			}
			for (CountingMeasure measure : countingMeasures) {
				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (SimulationPerformance performance : entry.getValue()) {
					long value = performance.getCountingMeasureResult(measure);
					if (value != SimulationPerformance.NO_COUNTING_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}
				long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				String valueAsString = averageOfValues + "";
				if (averageOfValues == 0) {
					valueAsString = "&ndash;";
				}
				row += separator + valueAsString;
			}
			table.add(row);
		}

		return table;
	}

	/**
	 * Creates a table that holds the time partitioning for each simulation type
	 * averaged over all automata instances respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createAveragedSimulationTimePartitioningTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Process performance list into a sorted map structure
		LinkedHashMap<Pair<SimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = new LinkedHashMap<>();
		for (LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (SimulationPerformance performanceOfSimulation : performanceComparison) {
				// Ignore timed out performances
				if (performanceOfSimulation.hasTimedOut()) {
					continue;
				}
				SimulationType type = performanceOfSimulation.getSimType();

				Pair<SimulationType, Boolean> simulationKey = new Pair<>(type, performanceOfSimulation.isUsingSCCs());
				LinkedList<SimulationPerformance> performances = simulationToPerformances.get(simulationKey);
				if (performances == null) {
					performances = new LinkedList<>();
					simulationToPerformances.put(simulationKey, performances);
				}
				performances.add(performanceOfSimulation);
			}
		}

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS";
		// Amount of Buechi states
		header += separator + CountingMeasure.BUCHI_STATES + "(&Oslash;)";
		// Overall time first
		header += separator + TimeMeasure.OVERALL_TIME + "(&Oslash;)";
		// Other time measures
		SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		Set<TimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (TimeMeasure measure : timeMeasures) {
			if (!measure.equals(TimeMeasure.OVERALL_TIME)) {
				header += separator + measure + "(%)(&Oslash;)";
			}
		}
		table.add(header);

		// Rows of table
		for (Entry<Pair<SimulationType, Boolean>, LinkedList<SimulationPerformance>> entry : simulationToPerformances
				.entrySet()) {
			String row = entry.getKey().getFirst() + separator + entry.getKey().getSecond();

			// Amount of Buechi states
			int sumOfAllValuesForBuechiStates = 0;
			int amountOfValuesForBuechiStates = 0;
			for (SimulationPerformance performance : entry.getValue()) {
				int value = performance.getCountingMeasureResult(CountingMeasure.BUCHI_STATES);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForBuechiStates += value;
				}
				amountOfValuesForBuechiStates++;
			}
			long averageOfValuesForBuechiStates = Math
					.round((sumOfAllValuesForBuechiStates + 0.0) / amountOfValuesForBuechiStates);
			String valueAsString = averageOfValuesForBuechiStates + "";
			if (averageOfValuesForBuechiStates == 0) {
				valueAsString = "&ndash;";
			}
			row += separator + valueAsString;

			// Overall time first
			long sumOfAllValuesForOverallTime = 0;
			int amountOfValuesForOverallTime = 0;
			for (SimulationPerformance performance : entry.getValue()) {
				long value = performance.getTimeMeasureResult(TimeMeasure.OVERALL_TIME, MultipleDataOption.ADDITIVE);
				if (value != SimulationPerformance.NO_TIME_RESULT) {
					sumOfAllValuesForOverallTime += value;
				}
				amountOfValuesForOverallTime++;
			}
			long averageOfValuesForOverallTime = Math
					.round((sumOfAllValuesForOverallTime + 0.0) / amountOfValuesForOverallTime);
			valueAsString = "";
			if (averageOfValuesForOverallTime == 0) {
				valueAsString = "&ndash;";
			} else {
				float valueInSeconds = millisToSeconds(averageOfValuesForOverallTime);
				valueAsString = valueInSeconds + "";
			}
			row += separator + valueAsString;

			// Other time measures
			for (TimeMeasure measure : timeMeasures) {
				if (measure.equals(TimeMeasure.OVERALL_TIME)) {
					continue;
				}

				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (SimulationPerformance performance : entry.getValue()) {
					long value = performance.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);
					if (value != SimulationPerformance.NO_TIME_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}
				long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				valueAsString = "";
				if (averageOfValues == 0 || averageOfValuesForOverallTime == 0) {
					valueAsString = "&ndash;";
				} else {
					int averageOfPercentages = percentageOf(averageOfValues, averageOfValuesForOverallTime);
					if (averageOfPercentages == 0) {
						valueAsString = "&ndash;";
					} else {
						valueAsString = averageOfPercentages + "";
					}
				}
				row += separator + valueAsString;

			}
			table.add(row);
		}

		return table;
	}

	/**
	 * Creates a table that holds the full comparison data for each automata
	 * instance respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createInstanceFullComparisonTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS" + separator + "TIMED_OUT";
		SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		Set<TimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (TimeMeasure measure : timeMeasures) {
			header += separator + measure;
		}
		Set<CountingMeasure> countingMeasures = headerCandidate.getCountingMeasures().keySet();
		for (CountingMeasure measure : countingMeasures) {
			header += separator + measure;
		}
		table.add(header);

		// Rows of table
		for (LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (SimulationPerformance performanceOfSimulation : performanceComparison) {
				SimulationType type = performanceOfSimulation.getSimType();

				// Fix fields
				String row = type + separator + performanceOfSimulation.isUsingSCCs() + separator
						+ performanceOfSimulation.hasTimedOut();

				// Variable fields
				for (TimeMeasure measure : timeMeasures) {
					long value = performanceOfSimulation.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);

					String valueAsString = "";
					if (value == SimulationPerformance.NO_TIME_RESULT) {
						valueAsString = "&ndash;";
					} else {
						float valueInSeconds = millisToSeconds(value);
						valueAsString = valueInSeconds + "";
					}

					row += separator + valueAsString;
				}
				for (CountingMeasure measure : countingMeasures) {
					int value = performanceOfSimulation.getCountingMeasureResult(measure);
					String valueAsString = value + "";
					if (value == SimulationPerformance.NO_COUNTING_RESULT) {
						valueAsString = "&ndash;";
					}
					row += separator + valueAsString;
				}
				table.add(row);
			}
			// Add empty row to delimit the performance entry
			table.add("");
		}

		return table;
	}

	/**
	 * Creates a table that holds the time partitioning for each automata
	 * instance respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createInstanceTimePartitioningTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS" + separator + "TIMED_OUT";
		// Amount of Buechi states
		header += separator + CountingMeasure.BUCHI_STATES;
		// Overall time first
		header += separator + TimeMeasure.OVERALL_TIME;
		// Other time measures
		SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		Set<TimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (TimeMeasure measure : timeMeasures) {
			if (!measure.equals(TimeMeasure.OVERALL_TIME)) {
				header += separator + measure + "(%)";
			}
		}
		table.add(header);

		// Rows of table
		for (LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (SimulationPerformance performanceOfSimulation : performanceComparison) {
				SimulationType type = performanceOfSimulation.getSimType();

				// Fix fields
				String row = type + separator + performanceOfSimulation.isUsingSCCs() + separator
						+ performanceOfSimulation.hasTimedOut();

				// Variable fields

				// Amount of Buechi states
				int buechiStates = performanceOfSimulation.getCountingMeasureResult(CountingMeasure.BUCHI_STATES);
				String buechiStatesAsString = buechiStates + "";
				if (buechiStates == SimulationPerformance.NO_COUNTING_RESULT) {
					buechiStatesAsString = "&ndash;";
				}
				row += separator + buechiStatesAsString;

				// Overall time first
				long value = performanceOfSimulation.getTimeMeasureResult(TimeMeasure.OVERALL_TIME,
						MultipleDataOption.ADDITIVE);

				String valueAsString = "";
				long overallTime = 0;
				if (value == SimulationPerformance.NO_TIME_RESULT) {
					valueAsString = "&ndash;";
				} else {
					float valueInSeconds = millisToSeconds(value);
					valueAsString = valueInSeconds + "";
					overallTime = value;
				}
				row += separator + valueAsString;

				// Other time measures
				for (TimeMeasure measure : timeMeasures) {
					if (measure.equals(TimeMeasure.OVERALL_TIME)) {
						continue;
					}

					// Calculate the percentage of the value to the overall time
					value = performanceOfSimulation.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);

					valueAsString = "";
					if (value == SimulationPerformance.NO_TIME_RESULT || overallTime == 0) {
						valueAsString = "&ndash;";
					} else {
						int percentage = percentageOf(value, overallTime);
						if (percentage == 0) {
							valueAsString = "&ndash;";
						} else {
							valueAsString = percentage + "";
						}
					}

					row += separator + valueAsString;
				}
				table.add(row);
			}
			// Add empty row to delimit the performance entry
			table.add("");
		}

		return table;
	}

	/**
	 * Converts a given long value, representing milliseconds, to seconds and
	 * rounds it to {@link #DECIMAL_PLACES} places after the decimal.
	 * 
	 * @param millis
	 *            Value, representing milliseconds, that should be converted
	 * @return The given value in seconds, rounded to two places after the
	 *         decimal.
	 */
	public static float millisToSeconds(final long millis) {
		BigDecimal secondsAsBigDecimal = new BigDecimal((millis + 0.0) / SECONDS_TO_MILLIS);
		secondsAsBigDecimal = secondsAsBigDecimal.setScale(DECIMAL_PLACES, RoundingMode.HALF_UP);
		float seconds = secondsAsBigDecimal.floatValue();
		return seconds;
	}

	/**
	 * Converts a given float value, representing seconds, to milliseconds.
	 * 
	 * @param seconds
	 *            Value, representing seconds, that should be converted
	 * @return The given value in milliseconds.
	 */
	public static long secondsToMillis(final float seconds) {
		return Math.round(seconds * SECONDS_TO_MILLIS);
	}

	/**
	 * Returns the percentage a given value has to a given full percentage.
	 * 
	 * @param value
	 *            Value to calculate percentage for
	 * @param fullPercentage
	 *            Number representing the full percentage
	 * @return Percentage of a given value to a given full percentage value
	 */
	private static int percentageOf(final long value, final long fullPercentage) {
		return (int) Math.round(((value + 0.0) / fullPercentage) * FULL_PERCENTAGE);
	}

	/**
	 * Utility class, private constructor.
	 */
	private ComparisonTables() {

	}
}
