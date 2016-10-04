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

import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Map.Entry;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ESimulationType;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Utility class that offers methods which create comparison tables for
 * performance analyze.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 *
 */
public final class ComparisonTables {

	/**
	 * Constant for representing no value.
	 */
	public static final String NO_VALUE = "NO_VALUE";
	/**
	 * Factor that, if multiplied with, converts seconds to milliseconds.
	 */
	public static final int SECONDS_TO_MILLIS = 1000;
	/**
	 * Decimal places to round duration of a method to.
	 */
	private static final int DECIMAL_PLACES = 3;
	/**
	 * Represents the value for full percentage.
	 */
	private static final int FULL_PERCENTAGE = 100;
	/**
	 * Amount of states at which a buechi automaton has a small size.
	 */
	private static final int SMALL_BUCHI_SIZE = 20;

	/**
	 * Creates a table that holds information about the actual work the
	 * algorithm needs to do for each simulation type averaged over all automata
	 * instances respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createAveragedSimulationAlgoWorkTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Process performance list into a sorted map structure
		final LinkedHashMap<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = calcSimToPerformances(
				performanceEntries);

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS";
		header += separator + ECountingMeasure.BUCHI_STATES;
		// Work measure
		header += separator + ECountingMeasure.SIMULATION_STEPS + " / " + ECountingMeasure.GAMEGRAPH_VERTICES;
		header += separator + ETimeMeasure.OVERALL;
		header += separator + ECountingMeasure.SIMULATION_STEPS;
		header += separator + ECountingMeasure.GAMEGRAPH_VERTICES;
		header += separator + ECountingMeasure.REMOVED_STATES;
		table.add(header);

		// Rows of table
		for (final Entry<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> entry : simulationToPerformances
				.entrySet()) {
			String row = entry.getKey().getFirst() + separator + entry.getKey().getSecond();

			// Amount of Buechi states
			int sumOfAllValuesForBuechiStates = 0;
			int amountOfValuesForBuechiStates = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final int value = performance.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForBuechiStates += value;
				}
				amountOfValuesForBuechiStates++;
			}
			final long averageOfValuesForBuechiStates = Math
					.round((sumOfAllValuesForBuechiStates + 0.0) / amountOfValuesForBuechiStates);
			String valueAsString = Long.toString(averageOfValuesForBuechiStates);
			if (averageOfValuesForBuechiStates == 0) {
				valueAsString = NO_VALUE;
			}
			row += separator + valueAsString;

			// Work measure
			int sumOfAllValuesForSimSteps = 0;
			int amountOfValuesForSimSteps = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final int value = performance.getCountingMeasureResult(ECountingMeasure.SIMULATION_STEPS);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForSimSteps += value;
				}
				amountOfValuesForSimSteps++;
			}
			final long averageOfValuesForSimSteps = Math
					.round((sumOfAllValuesForSimSteps + 0.0) / amountOfValuesForSimSteps);
			int sumOfAllValuesForGraphStates = 0;
			int amountOfValuesForGraphStates = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final int value = performance.getCountingMeasureResult(ECountingMeasure.GAMEGRAPH_VERTICES);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForGraphStates += value;
				}
				amountOfValuesForGraphStates++;
			}
			final long averageOfValuesForGraphStates = Math
					.round((sumOfAllValuesForGraphStates + 0.0) / amountOfValuesForGraphStates);
			if (averageOfValuesForSimSteps == 0 || averageOfValuesForGraphStates == 0) {
				valueAsString = NO_VALUE;
			} else {
				valueAsString = Float.toString(roundTo((averageOfValuesForSimSteps + 0.0) / averageOfValuesForGraphStates,
						DECIMAL_PLACES));
			}
			row += separator + valueAsString;

			// Overall time
			long sumOfAllValuesForOverallTime = 0;
			int amountOfValuesForOverallTime = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final long value = performance.getTimeMeasureResult(ETimeMeasure.OVERALL, EMultipleDataOption.ADDITIVE);
				if (value != SimulationPerformance.NO_TIME_RESULT) {
					sumOfAllValuesForOverallTime += value;
				}
				amountOfValuesForOverallTime++;
			}
			final long averageOfValuesForOverallTime = Math
					.round((sumOfAllValuesForOverallTime + 0.0) / amountOfValuesForOverallTime);
			if (averageOfValuesForOverallTime == 0) {
				valueAsString = NO_VALUE;
			} else {
				final float valueInSeconds = millisToSeconds(averageOfValuesForOverallTime);
				valueAsString = Float.toString(valueInSeconds);
			}
			row += separator + valueAsString;

			// Simulation steps
			valueAsString = Long.toString(averageOfValuesForSimSteps);
			if (averageOfValuesForSimSteps == 0) {
				valueAsString = NO_VALUE;
			}
			row += separator + valueAsString;

			// Gamegraph states
			valueAsString = Long.toString(averageOfValuesForGraphStates);
			if (averageOfValuesForGraphStates == 0) {
				valueAsString = NO_VALUE;
			}
			row += separator + valueAsString;

			// Amount of removed states
			int sumOfAllValuesForRemovedStates = 0;
			int amountOfValuesForRemovedStates = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final int value = performance.getCountingMeasureResult(ECountingMeasure.REMOVED_STATES);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForRemovedStates += value;
				}
				amountOfValuesForRemovedStates++;
			}
			final long averageOfValuesForRemovedStates = Math
					.round((sumOfAllValuesForRemovedStates + 0.0) / amountOfValuesForRemovedStates);
			valueAsString = Long.toString(averageOfValuesForRemovedStates);
			if (averageOfValuesForRemovedStates == 0) {
				valueAsString = NO_VALUE;
			}
			row += separator + valueAsString;

			table.add(row);
		}

		return table;
	}

	/**
	 * Creates a table that holds the full comparison data for each simulation
	 * type averaged over all automata instances respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @param simulationType
	 *            The simulation type interested in, or <tt>null</tt> if
	 *            interested in all results
	 * @param filtered
	 *            If the result should not contain results where the input
	 *            automaton has an empty size, at least one of the methods timed
	 *            out or an OutOfMemory-Error occurred.
	 * @param filterOnlyNwa
	 *            If the result should only contain nested word automaton, this
	 *            removes every automaton which has no return transitions
	 * @param convertTransitionDensityToDouble
	 *            Converts transition density values from Integer back to
	 *            Double.
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createAveragedSimulationFullComparisonTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator,
			final ESimulationType simulationType, final boolean filtered, final boolean filterOnlyNwa,
			final boolean convertTransitionDensityToDouble) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Process performance list into a sorted map structure
		final LinkedHashMap<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = calcSimToPerformances(
				performanceEntries);

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS";
		final SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		final Set<ETimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (final ETimeMeasure measure : timeMeasures) {
			header += separator + measure;
		}
		final Set<ECountingMeasure> countingMeasures = headerCandidate.getCountingMeasures().keySet();
		for (final ECountingMeasure measure : countingMeasures) {
			header += separator + measure;
		}
		table.add(header);

		// Rows of table
		for (final Entry<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> entry : simulationToPerformances
				.entrySet()) {
			if (simulationType != null && entry.getKey().getFirst() != simulationType) {
				// If we are interested in a explicit simulation, ignore other
				// results
				continue;
			}

			String row = entry.getKey().getFirst() + separator + entry.getKey().getSecond();

			final Map<SimulationPerformance, Boolean> ignoreThisPerformance = new HashMap<>();
			if (filtered || filterOnlyNwa) {
				for (final SimulationPerformance performance : entry.getValue()) {
					if (filtered) {
						// If filtering, we are not interested in this
						// comparison if
						// the automaton is empty, a simulation had OOM or timed
						// out
						final int size = performance.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
						if (performance.hasTimedOut() || performance.isOutOfMemory() || size == 0
								|| size == SimulationPerformance.NO_COUNTING_RESULT) {
							ignoreThisPerformance.put(performance, true);
						}
					}
					if (filterOnlyNwa) {
						// In this case every automaton that has no return
						// transitions should get removed
						final int returnTransitions = performance
								.getCountingMeasureResult(ECountingMeasure.BUCHI_TRANSITIONS_RETURN);
						if (returnTransitions == 0 || returnTransitions == SimulationPerformance.NO_COUNTING_RESULT) {
							ignoreThisPerformance.put(performance, true);
						}
					}
				}
			}

			for (final ETimeMeasure measure : timeMeasures) {
				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (final SimulationPerformance performance : entry.getValue()) {
					if (ignoreThisPerformance.get(performance) != null && ignoreThisPerformance.get(performance)) {
						continue;
					}

					final long value = performance.getTimeMeasureResult(measure, EMultipleDataOption.ADDITIVE);
					if (value != SimulationPerformance.NO_TIME_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}
				final long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				String valueAsString;
				if (averageOfValues == 0) {
					valueAsString = NO_VALUE;
				} else {
					final float valueInSeconds = millisToSeconds(averageOfValues);
					valueAsString = Float.toString(valueInSeconds);
				}

				row += separator + valueAsString;

			}
			for (final ECountingMeasure measure : countingMeasures) {
				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (final SimulationPerformance performance : entry.getValue()) {
					if (ignoreThisPerformance.get(performance) != null && ignoreThisPerformance.get(performance)) {
						continue;
					}

					final long value = performance.getCountingMeasureResult(measure);
					if (value != SimulationPerformance.NO_COUNTING_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}

				final long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				String valueAsString = Long.toString(averageOfValues);
				if (averageOfValues == 0) {
					valueAsString = NO_VALUE;
				}
				if (convertTransitionDensityToDouble) {
					final Double sumOfAllValuesAsDouble = convertTransitionDensityToDouble(measure, sumOfAllValues);
					if (sumOfAllValuesAsDouble != null) {
						final double averageOfValuesAsDouble = sumOfAllValuesAsDouble / amountOfValues;
						valueAsString = Double.toString(averageOfValuesAsDouble);
						if (averageOfValuesAsDouble == 0.0) {
							valueAsString = NO_VALUE;
						}
					}
				}
				row += separator + valueAsString;
			}
			table.add(row);
		}

		return table;
	}

	/**
	 * Creates a table that holds the time partitioning for each simulation type
	 * averaged over all automata instances respectively. The work measure gets
	 * calculated by (SIMULATION_STEPS / GAMEGRAPH_STATES).
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
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Process performance list into a sorted map structure
		final LinkedHashMap<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = calcSimToPerformances(
				performanceEntries);

		// Header of table
		String header = "TYPE" + separator + "USED_SCCS";
		// Amount of Buechi states
		header += separator + ECountingMeasure.BUCHI_STATES;
		// Overall time first
		header += separator + ETimeMeasure.OVERALL;
		// Other time measures
		final SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		final Set<ETimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (final ETimeMeasure measure : timeMeasures) {
			if (!measure.equals(ETimeMeasure.OVERALL)) {
				header += separator + measure;
			}
		}
		table.add(header);

		// Rows of table
		for (final Entry<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> entry : simulationToPerformances
				.entrySet()) {
			String row = entry.getKey().getFirst() + separator + entry.getKey().getSecond();

			// Amount of Buechi states
			int sumOfAllValuesForBuechiStates = 0;
			int amountOfValuesForBuechiStates = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final int value = performance.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
				if (value != SimulationPerformance.NO_COUNTING_RESULT) {
					sumOfAllValuesForBuechiStates += value;
				}
				amountOfValuesForBuechiStates++;
			}
			final long averageOfValuesForBuechiStates = Math
					.round((sumOfAllValuesForBuechiStates + 0.0) / amountOfValuesForBuechiStates);
			String valueAsString = Long.toString(averageOfValuesForBuechiStates);
			if (averageOfValuesForBuechiStates == 0) {
				valueAsString = NO_VALUE;
			}
			row += separator + valueAsString;

			// Overall time first
			long sumOfAllValuesForOverallTime = 0;
			int amountOfValuesForOverallTime = 0;
			for (final SimulationPerformance performance : entry.getValue()) {
				final long value = performance.getTimeMeasureResult(ETimeMeasure.OVERALL, EMultipleDataOption.ADDITIVE);
				if (value != SimulationPerformance.NO_TIME_RESULT) {
					sumOfAllValuesForOverallTime += value;
				}
				amountOfValuesForOverallTime++;
			}
			final long averageOfValuesForOverallTime = Math
					.round((sumOfAllValuesForOverallTime + 0.0) / amountOfValuesForOverallTime);
			if (averageOfValuesForOverallTime == 0) {
				valueAsString = NO_VALUE;
			} else {
				final float valueInSeconds = millisToSeconds(averageOfValuesForOverallTime);
				valueAsString = Float.toString(valueInSeconds);
			}
			row += separator + valueAsString;

			// Other time measures
			for (final ETimeMeasure measure : timeMeasures) {
				if (measure.equals(ETimeMeasure.OVERALL)) {
					continue;
				}

				long sumOfAllValues = 0;
				int amountOfValues = 0;
				for (final SimulationPerformance performance : entry.getValue()) {
					final long value = performance.getTimeMeasureResult(measure, EMultipleDataOption.ADDITIVE);
					if (value != SimulationPerformance.NO_TIME_RESULT) {
						sumOfAllValues += value;
					}
					amountOfValues++;
				}
				final long averageOfValues = Math.round((sumOfAllValues + 0.0) / amountOfValues);
				if (averageOfValues == 0 || averageOfValuesForOverallTime == 0) {
					valueAsString = NO_VALUE;
				} else {
					final int averageOfPercentages = percentageOf(averageOfValues, averageOfValuesForOverallTime);
					if (averageOfPercentages == 0) {
						valueAsString = NO_VALUE;
					} else {
						valueAsString = Integer.toString(averageOfPercentages);
					}
				}
				row += separator + valueAsString;

			}
			table.add(row);
		}

		return table;
	}

	/**
	 * Creates a table that holds information about the actual work the
	 * algorithm needs to do for each automata instance respectively. The work
	 * measure gets calculated by (SIMULATION_STEPS / GAMEGRAPH_STATES).
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createInstanceAlgoWorkTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "NAME" + separator + "TYPE" + separator + "USED_SCCS" + separator + "TIMED_OUT" + separator
				+ "OOM";
		header += separator + ECountingMeasure.BUCHI_STATES;
		// Work measure
		header += separator + ECountingMeasure.SIMULATION_STEPS + " / " + ECountingMeasure.GAMEGRAPH_VERTICES;
		header += separator + ETimeMeasure.OVERALL;
		header += separator + ECountingMeasure.SIMULATION_STEPS;
		header += separator + ECountingMeasure.GAMEGRAPH_VERTICES;
		header += separator + ECountingMeasure.REMOVED_STATES;

		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				final ESimulationType type = performanceOfSimulation.getSimType();
				final String name = performanceOfSimulation.getName();

				// Fix fields
				String row = name + separator + type + separator + performanceOfSimulation.isUsingSCCs() + separator
						+ performanceOfSimulation.hasTimedOut() + separator + performanceOfSimulation.isOutOfMemory();

				// Variable fields

				// Amount of Buechi states
				final int buechiStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
				String buechiStatesAsString = Integer.toString(buechiStates);
				if (buechiStates == SimulationPerformance.NO_COUNTING_RESULT) {
					buechiStatesAsString = NO_VALUE;
				}
				row += separator + buechiStatesAsString;

				// Work measure
				final int simSteps = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.SIMULATION_STEPS);
				final int graphStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.GAMEGRAPH_VERTICES);
				String workMeasureAsString;
				if (simSteps == SimulationPerformance.NO_COUNTING_RESULT
						|| graphStates == SimulationPerformance.NO_COUNTING_RESULT) {
					workMeasureAsString = NO_VALUE;
				} else {
					workMeasureAsString = Float.toString(roundTo((simSteps + 0.0) / graphStates, DECIMAL_PLACES));
				}
				row += separator + workMeasureAsString;

				// Overall time
				final long value = performanceOfSimulation.getTimeMeasureResult(ETimeMeasure.OVERALL,
						EMultipleDataOption.ADDITIVE);

				String valueAsString;
				if (value == SimulationPerformance.NO_TIME_RESULT) {
					valueAsString = NO_VALUE;
				} else {
					final float valueInSeconds = millisToSeconds(value);
					valueAsString = Float.toString(valueInSeconds);
				}
				row += separator + valueAsString;

				// Simulation steps
				String simStepsAsString;
				if (simSteps == SimulationPerformance.NO_COUNTING_RESULT) {
					simStepsAsString = NO_VALUE;
				} else {
					simStepsAsString = Integer.toString(simSteps);
				}
				row += separator + simStepsAsString;

				// Amount of Gamegraph states
				String graphStatesAsString = Integer.toString(graphStates);
				if (graphStates == SimulationPerformance.NO_COUNTING_RESULT) {
					graphStatesAsString = NO_VALUE;
				}
				row += separator + graphStatesAsString;

				// Removed states
				final int removedStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.REMOVED_STATES);
				String removedStatesAsString = Integer.toString(removedStates);
				if (removedStates == SimulationPerformance.NO_COUNTING_RESULT) {
					removedStatesAsString = NO_VALUE;
				}
				row += separator + removedStatesAsString;

				table.add(row);
			}
			// Add empty row to delimit the performance entry
			table.add("");
		}

		return table;
	}

	/**
	 * Creates a table that holds the full comparison data for each automata
	 * instance respectively, but only for the given simulation type.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @param separator
	 *            Separator to use for separating cells
	 * @param simulationType
	 *            The simulation type interested in, or <tt>null</tt> if
	 *            interested in all results
	 * @param filtered
	 *            If the result should not contain results where the input
	 *            automaton has an empty size, at least one of the methods timed
	 *            out or an OutOfMemory-Error occurred.
	 * @param filterOnlyNwa
	 *            If the result should only contain nested word automaton, this
	 *            removes every automaton which has no return transitions
	 * @param convertTransitionDensityToDouble
	 *            Converts transition density values from Integer back to
	 *            Double.
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createInstanceFullComparisonTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries, final String separator,
			final ESimulationType simulationType, final boolean filtered, final boolean filterOnlyNwa,
			final boolean convertTransitionDensityToDouble) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "NAME" + separator + "TYPE" + separator + "USED_SCCS" + separator + "TIMED_OUT" + separator
				+ "OOM";
		final SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		final Set<ETimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (final ETimeMeasure measure : timeMeasures) {
			header += separator + measure;
		}
		final Set<ECountingMeasure> countingMeasures = headerCandidate.getCountingMeasures().keySet();
		for (final ECountingMeasure measure : countingMeasures) {
			header += separator + measure;
		}
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				final ESimulationType type = performanceOfSimulation.getSimType();
				final String name = performanceOfSimulation.getName();

				// We are only interested in results of the given simulation
				// type, if set
				if (simulationType != null && !type.equals(simulationType)) {
					continue;
				}
				if (filtered) {
					// If filtering, we are not interested in this comparison if
					// the automaton is empty, a simulation had OOM or timed out
					final int size = performanceOfSimulation.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
					if (performanceOfSimulation.hasTimedOut() || performanceOfSimulation.isOutOfMemory() || size == 0
							|| size == SimulationPerformance.NO_COUNTING_RESULT) {
						break;
					}
				}
				if (filterOnlyNwa) {
					// In this case every automaton that has no return
					// transitions should get removed
					final int returnTransitions = performanceOfSimulation
							.getCountingMeasureResult(ECountingMeasure.BUCHI_TRANSITIONS_RETURN);
					if (returnTransitions == 0 || returnTransitions == SimulationPerformance.NO_COUNTING_RESULT) {
						break;
					}
				}

				// Fix fields
				String row = name + separator + type + separator + performanceOfSimulation.isUsingSCCs() + separator
						+ performanceOfSimulation.hasTimedOut() + separator + performanceOfSimulation.isOutOfMemory();

				// Variable fields
				for (final ETimeMeasure measure : timeMeasures) {
					final long value = performanceOfSimulation.getTimeMeasureResult(measure,
							EMultipleDataOption.ADDITIVE);

					String valueAsString;
					if (value == SimulationPerformance.NO_TIME_RESULT) {
						valueAsString = NO_VALUE;
					} else {
						final float valueInSeconds = millisToSeconds(value);
						valueAsString = Float.toString(valueInSeconds);
					}

					row += separator + valueAsString;
				}
				for (final ECountingMeasure measure : countingMeasures) {
					final int value = performanceOfSimulation.getCountingMeasureResult(measure);

					String valueAsString = Integer.toString(value);
					if (value == SimulationPerformance.NO_COUNTING_RESULT) {
						valueAsString = NO_VALUE;
					} else {
						if (convertTransitionDensityToDouble) {
							final Double valueAsDouble = convertTransitionDensityToDouble(measure, value);
							if (valueAsDouble != null) {
								valueAsString = Double.toString(valueAsDouble);
							}
						}
					}
					row += separator + valueAsString;
				}
				table.add(row);
			}
			if (simulationType == null) {
				// Add empty row to delimit the performance entry
				table.add("");
			}
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
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "NAME" + separator + "TYPE" + separator + "USED_SCCS" + separator + "TIMED_OUT" + separator
				+ "OOM";
		// Amount of Buechi states
		header += separator + ECountingMeasure.BUCHI_STATES;
		// Overall time first
		header += separator + ETimeMeasure.OVERALL;
		// Other time measures
		final SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		final Set<ETimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (final ETimeMeasure measure : timeMeasures) {
			if (!measure.equals(ETimeMeasure.OVERALL)) {
				header += separator + measure + "(%)";
			}
		}
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				final ESimulationType type = performanceOfSimulation.getSimType();
				final String name = performanceOfSimulation.getName();

				// Fix fields
				String row = name + separator + type + separator + performanceOfSimulation.isUsingSCCs() + separator
						+ performanceOfSimulation.hasTimedOut() + separator + performanceOfSimulation.isOutOfMemory();

				// Variable fields

				// Amount of Buechi states
				final int buechiStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
				String buechiStatesAsString;
				if (buechiStates == SimulationPerformance.NO_COUNTING_RESULT) {
					buechiStatesAsString = NO_VALUE;
				} else {
					buechiStatesAsString = Integer.toString(buechiStates);
				}
				row += separator + buechiStatesAsString;

				// Overall time first
				long value = performanceOfSimulation.getTimeMeasureResult(ETimeMeasure.OVERALL,
						EMultipleDataOption.ADDITIVE);

				String valueAsString;
				long overallTime = 0;
				if (value == SimulationPerformance.NO_TIME_RESULT) {
					valueAsString = NO_VALUE;
				} else {
					final float valueInSeconds = millisToSeconds(value);
					valueAsString = Float.toString(valueInSeconds);
					overallTime = value;
				}
				row += separator + valueAsString;

				// Other time measures
				for (final ETimeMeasure measure : timeMeasures) {
					if (measure.equals(ETimeMeasure.OVERALL)) {
						continue;
					}

					// Calculate the percentage of the value to the overall time
					value = performanceOfSimulation.getTimeMeasureResult(measure, EMultipleDataOption.ADDITIVE);

					if (value == SimulationPerformance.NO_TIME_RESULT || overallTime == 0) {
						valueAsString = NO_VALUE;
					} else {
						final int percentage = percentageOf(value, overallTime);
						if (percentage == 0) {
							valueAsString = NO_VALUE;
						} else {
							valueAsString = Integer.toString(percentage);
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
	 * Creates a table that holds all names of automata where the overall time
	 * needed was greater than one second.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createLongerThanOneSecondNamesTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		final String header = "NAME";
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean buechiLongerThanOneSecond = false;
			String name = "";
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				name = performanceOfSimulation.getName();
				final long overallTime = performanceOfSimulation.getTimeMeasureResult(ETimeMeasure.OVERALL,
						EMultipleDataOption.ADDITIVE);
				if (overallTime != SimulationPerformance.NO_TIME_RESULT && overallTime > SECONDS_TO_MILLIS) {
					buechiLongerThanOneSecond = true;
					break;
				}
			}
			if (buechiLongerThanOneSecond) {
				table.add(name);
			}
		}

		return table;
	}

	/**
	 * Creates a table that holds all names of automata where no method could
	 * remove states.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createNoRemoveNamesTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		final String header = "NAME";
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean methodHasRemoved = false;
			String name = "";
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				name = performanceOfSimulation.getName();
				final int amountOfRemovedStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.REMOVED_STATES);
				if (amountOfRemovedStates != SimulationPerformance.NO_COUNTING_RESULT && amountOfRemovedStates > 0) {
					methodHasRemoved = true;
					break;
				}
			}
			if (!methodHasRemoved) {
				table.add(name);
			}
		}

		return table;
	}

	/**
	 * Creates a table that holds all names of automata where the amount of
	 * states is small, i.e. less than 20.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createSmallSizeNamesTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		final String header = "NAME";
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean buechiHasSmallSize = false;
			String name = "";
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				name = performanceOfSimulation.getName();
				final int amountOfStates = performanceOfSimulation
						.getCountingMeasureResult(ECountingMeasure.BUCHI_STATES);
				if (amountOfStates == SimulationPerformance.NO_COUNTING_RESULT || amountOfStates < SMALL_BUCHI_SIZE) {
					buechiHasSmallSize = true;
					break;
				}
			}
			if (buechiHasSmallSize) {
				table.add(name);
			}
		}

		return table;
	}

	/**
	 * Creates a table that holds all names of automata where at least one
	 * method timed out.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	public static List<String> createTimedOutNamesTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		final List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		final String header = "NAME";
		table.add(header);

		// Rows of table
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean methodTimedOut = false;
			String name = "";
			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				name = performanceOfSimulation.getName();
				if (performanceOfSimulation.hasTimedOut()) {
					methodTimedOut = true;
					break;
				}
			}
			if (methodTimedOut) {
				table.add(name);
			}
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
		return roundTo((millis + 0.0) / SECONDS_TO_MILLIS, DECIMAL_PLACES);
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
	 * Processes a given performance list into a sorted map structure. A
	 * performance entry is completely ignored if one simulation of it had a
	 * timeout.
	 * 
	 * @param performanceEntries
	 *            List of performances to process
	 * @return Performance entries in a sorted map structure
	 */
	private static LinkedHashMap<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> calcSimToPerformances(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		// Process performance list into a sorted map structure
		final LinkedHashMap<Pair<ESimulationType, Boolean>, LinkedList<SimulationPerformance>> simulationToPerformances = new LinkedHashMap<>();
		for (final LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			boolean simulationOfComparisonHasTimedOut = false;
			boolean simulationOfComparisonWasOutOfMemory = false;
			final LinkedList<SimulationPerformance> performancesToAdd = new LinkedList<>();

			for (final SimulationPerformance performanceOfSimulation : performanceComparison) {
				// Ignore comparison if a simulation has timed out or was out of
				// memory
				if (performanceOfSimulation.hasTimedOut()) {
					simulationOfComparisonHasTimedOut = true;
					break;
				} else if (performanceOfSimulation.isOutOfMemory()) {
					simulationOfComparisonWasOutOfMemory = true;
					break;
				}

				performancesToAdd.add(performanceOfSimulation);
			}
			if (!simulationOfComparisonHasTimedOut && !simulationOfComparisonWasOutOfMemory) {
				// No timeout and no out of memory occurred, add performances
				for (final SimulationPerformance performance : performancesToAdd) {
					final ESimulationType type = performance.getSimType();

					final Pair<ESimulationType, Boolean> simulationKey = new Pair<>(type, performance.isUsingSCCs());
					LinkedList<SimulationPerformance> performances = simulationToPerformances.get(simulationKey);
					if (performances == null) {
						performances = new LinkedList<>();
						simulationToPerformances.put(simulationKey, performances);
					}
					performances.add(performance);
				}
			}
		}
		return simulationToPerformances;
	}

	/**
	 * Converts the given value to a double format if the given measure is a
	 * transition density measure.
	 * 
	 * @param measure
	 *            Current measure
	 * @param sumOfAllValues
	 *            Value to convert
	 * @return The given value in a double format if the given measure is a
	 *         transition density measure or <tt>null</tt> if it is not.
	 */
	private static Double convertTransitionDensityToDouble(final ECountingMeasure measure, final long sumOfAllValues) {
		if (measure == ECountingMeasure.BUCHI_TRANSITION_DENSITY_MILLION
				|| measure == ECountingMeasure.BUCHI_TRANSITION_INTERNAL_DENSITY_MILLION
				|| measure == ECountingMeasure.BUCHI_TRANSITION_CALL_DENSITY_MILLION
				|| measure == ECountingMeasure.BUCHI_TRANSITION_RETURN_DENSITY_MILLION
				|| measure == ECountingMeasure.RESULT_TRANSITION_DENSITY_MILLION
				|| measure == ECountingMeasure.RESULT_TRANSITION_INTERNAL_DENSITY_MILLION
				|| measure == ECountingMeasure.RESULT_TRANSITION_CALL_DENSITY_MILLION
				|| measure == ECountingMeasure.RESULT_TRANSITION_RETURN_DENSITY_MILLION) {
			final double million = 1_000_000.0;
			return (sumOfAllValues + 0.0) / million;
		} else {
			return null;
		}
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
	 * Rounds a given value to a given scale.
	 * 
	 * @param value
	 *            Value to round
	 * @param scale
	 *            Scale to round to
	 * @return The rounded value
	 */
	private static float roundTo(final double value, final int scale) {
		BigDecimal valueAsBigDecimal = new BigDecimal(value);
		valueAsBigDecimal = valueAsBigDecimal.setScale(scale, RoundingMode.HALF_UP);
		return valueAsBigDecimal.floatValue();
	}

	/**
	 * Utility class, private constructor.
	 */
	private ComparisonTables() {

	}
}
