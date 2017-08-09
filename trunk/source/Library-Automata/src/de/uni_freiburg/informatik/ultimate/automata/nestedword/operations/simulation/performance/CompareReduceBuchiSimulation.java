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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileFilter;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveDeadEnds;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.IMinimizationStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSat;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeNwaPmaxSatDirect;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.SimulationOrMinimizationType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.DelayedGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.delayed.DelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.DirectGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.FairDirectGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.FairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.FairGameGraph;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.fair.FairSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.FullMultipebbleGameState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.multipebble.ReduceNwaFullMultipebbleSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Operation that compares the different types of simulation methods for buechi reduction.<br/>
 * The resulting automaton is the input automaton.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public class CompareReduceBuchiSimulation<LETTER, STATE>
		extends UnaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * Constant for representing no value in the html format.
	 */
	public static final String HTML_NO_VALUE = "&ndash;";
	/**
	 * Path where simulation performance relevant logs and data gets saved.
	 */
	public static final File LOG_PATH =
			new File(new File(System.getProperty("user.home"), "Desktop"), "simulationPerformance");
	/**
	 * Separator that is used in the log.
	 */
	public static final String LOG_SEPARATOR = "\t";
	/**
	 * Constant for representing no value in the plot format.
	 */
	public static final String PLOT_NO_VALUE = "--";
	/**
	 * Separator that is used in plot files.
	 */
	public static final String PLOT_SEPARATOR = "\t";
	/**
	 * Amount of fix fields in the log format. Currently this is name, type, usedSCCs, timedOut and outOfMemory.
	 */
	private static final int FIX_FIELD_AMOUNT = 5;
	/**
	 * Marks the end of the head from an entry.
	 */
	private static final String LOG_ENTRY_HEAD_END = "-->";
	/**
	 * Marks the start of the head from an entry.
	 */
	private static final String LOG_ENTRY_HEAD_START = "<!--";
	/**
	 * Threshold in bytes at which a log file should get finalized.
	 */
	private static final int LOG_FILE_SIZE_THRESHOLD = 1_000_000;
	/**
	 * Name for the object of the log file.
	 */
	private static final String LOG_PATH_DATA = "testData";
	/**
	 * Extension for the object of the log file.
	 */
	private static final String LOG_PATH_DATA_EXT = ".tsv";
	/**
	 * Prefix for test result files.
	 */
	private static final String LOG_PATH_HTML_PRE = "testResults_";
	/**
	 * Suffix for test result files.
	 */
	private static final String LOG_PATH_HTML_SUFF = ".html";
	/**
	 * Prefix for test result files.
	 */
	private static final String LOG_PATH_PLOT_PRE = "plot_";
	/**
	 * Suffix for test result files.
	 */
	private static final String LOG_PATH_PLOT_SUFF = ".csv";

	/**
	 * Time in seconds after which a simulation method should timeout.
	 */
	private static final int SIMULATION_TIMEOUT = 10;

	/**
	 * Holds counting measures of the comparison.
	 */
	protected final LinkedHashMap<CountingMeasure, Integer> mCountingMeasures;
	/**
	 * Overall time an external operation took. Needed since it does not track this measure by itself.
	 */
	private long mExternalOverallTime;
	/**
	 * Filter for logging files.
	 */
	private final FileFilter mLogFileFilter;
	/**
	 * Internal buffer for logged lines, can be flushed by using {@link #flushLogToLogger()}.
	 */
	private final List<String> mLoggedLines;
	/**
	 * The inputed buechi automaton.
	 */
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mOperand;
	/**
	 * Holds time measures of the comparison.
	 */
	private final LinkedHashMap<TimeMeasure, Float> mTimeMeasures;

	/**
	 * Compares the different types of simulation methods for buechi reduction. Resulting automaton is the input
	 * automaton.
	 * <p>
	 * Throws an IllegalArgumentException If the input automaton is no Buchi automaton. It must have an empty call and
	 * return alphabet.
	 *
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to compare with
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public CompareReduceBuchiSimulation(final AutomataLibraryServices services,
			final IMinimizationStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) throws AutomataOperationCanceledException {
		super(services);
		verifyAutomatonValidity(operand);

		mLoggedLines = new LinkedList<>();
		mOperand = operand;
		mTimeMeasures = new LinkedHashMap<>();
		mCountingMeasures = new LinkedHashMap<>();
		mExternalOverallTime = 0;
		mLogFileFilter = new FileFilter() {
			/*
			 * (non-Javadoc)
			 *
			 * @see java.io.FileFilter#accept(java.io.File)
			 */
			@Override
			public boolean accept(final File pathname) {
				final String name = pathname.getName();
				return name.startsWith(LOG_PATH_DATA) && name.endsWith(LOG_PATH_DATA_EXT);
			}
		};

		mLogger.info(startMessage());

		createAndResetPerformanceHead();
		appendPerformanceHeadToLog();

		final long simulationTimeoutMillis = SIMULATION_TIMEOUT * ComparisonTables.SECONDS_TO_MILLIS;

		// Remove dead ends, a requirement of simulation
		final NestedWordAutomatonReachableStates<LETTER, STATE> operandReachable =
				new RemoveUnreachable<>(mServices, new RemoveDeadEnds<>(mServices, operand).getResult()).getResult();

		final String automatonName = "";
		// BufferedReader br = null;
		// try {
		// br = new BufferedReader(new FileReader(new File(LOG_PATH, "currentAutomatonName.txt")));
		// while (br.ready()) {
		// automatonName = br.readLine();
		// }
		// } catch (IOException e) {
		// e.printStackTrace();
		// } finally {
		// if (br != null) {
		// try {
		// br.close();
		// } catch (IOException e) {
		// e.printStackTrace();
		// }
		// }
		// }

		measurePerformances(automatonName, simulationTimeoutMillis, stateFactory, operandReachable);

		// flushLogToLogger();
		flushLogToFile();

		mLogger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public String getResult() {
		return "no result";
	}

	/**
	 * Verifies the validity of a given automaton. If the automaton is not valid it throws an
	 * {@link IllegalArgumentException}.
	 *
	 * @param automaton
	 *            Automaton to verify validity
	 */
	public void verifyAutomatonValidity(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton) {
		if (!NestedWordAutomataUtils.isFiniteAutomaton(automaton)) {
			throw new IllegalArgumentException(
					"The inputed automaton is no Buechi-automaton. It must have an empty call and return alphabet.");
		}
	}

	/**
	 * Appends the current saved state of the performance as an entry to the log.
	 *
	 * @param name
	 *            Name of the automaton used for the method
	 * @param type
	 *            Type of the used method
	 * @param usedSCCs
	 *            If SCCs where used by the method
	 * @param timedOut
	 *            If the method timed out
	 * @param outOfMemory
	 *            If the method has thrown an out of memory error
	 */
	private void appendCurrentPerformanceEntryToLog(final String name, final SimulationOrMinimizationType type,
			final boolean usedSCCs, final boolean timedOut, final boolean outOfMemory) {
		// Fix fields
		String message = name + LOG_SEPARATOR + type + LOG_SEPARATOR + usedSCCs + LOG_SEPARATOR + timedOut
				+ LOG_SEPARATOR + outOfMemory;
		// Variable fields
		for (final Float measureValue : mTimeMeasures.values()) {
			message += LOG_SEPARATOR + measureValue;
		}
		for (final Integer measureValue : mCountingMeasures.values()) {
			message += LOG_SEPARATOR + measureValue;
		}
		logLine(message);
	}

	/**
	 * Appends the head of the performance format to the log.
	 */
	private void appendPerformanceHeadToLog() {
		String message = LOG_ENTRY_HEAD_START + LOG_SEPARATOR;

		// Fix fields
		message += "NAME" + LOG_SEPARATOR + "TYPE" + LOG_SEPARATOR + "USED_SCCS" + LOG_SEPARATOR + "TIMED_OUT"
				+ LOG_SEPARATOR + "OOM" + LOG_SEPARATOR;
		// Variable fields
		for (final TimeMeasure measure : mTimeMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}
		for (final CountingMeasure measure : mCountingMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}

		message += LOG_ENTRY_HEAD_END;

		logLine(message);
	}

	/**
	 * Creates or resets the head of the performance format.
	 */
	private void createAndResetPerformanceHead() {
		for (final TimeMeasure measure : TimeMeasure.values()) {
			mTimeMeasures.put(measure, (float) SimulationPerformance.NO_TIME_RESULT);
		}
		for (final CountingMeasure measure : CountingMeasure.values()) {
			mCountingMeasures.put(measure, SimulationPerformance.NO_COUNTING_RESULT);
		}
	}

	/**
	 * Creates an out of memory performance object and adds some information of the used method.
	 *
	 * @param name
	 *            Name of the performance object
	 * @param type
	 *            Type of the simulation
	 * @param useSCCs
	 *            If the simulation usedSCCs
	 * @param operand
	 *            Operand the simulation processed
	 * @return The out of memory performance object
	 */
	private SimulationPerformance createOutOfMemoryPerformance(final String name,
			final SimulationOrMinimizationType type, final boolean useSCCs,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		final SimulationPerformance performance = SimulationPerformance.createOutOfMemoryPerformance(type, useSCCs);
		performance.setName(name);
		performance.setCountingMeasure(CountingMeasure.BUCHI_STATES, operand.size());
		return performance;
	}

	/**
	 * Creates a timed out performance object and adds some information of the timed out method.
	 *
	 * @param name
	 *            Name of the performance object
	 * @param type
	 *            Type of the simulation
	 * @param useSCCs
	 *            If the simulation usedSCCs
	 * @param operand
	 *            Operand the simulation processed
	 * @return The timed out performance object
	 */
	private SimulationPerformance createTimedOutPerformance(final String name, final SimulationOrMinimizationType type,
			final boolean useSCCs, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		final SimulationPerformance performance = SimulationPerformance.createTimedOutPerformance(type, useSCCs);
		performance.setName(name);
		performance.setCountingMeasure(CountingMeasure.BUCHI_STATES, operand.size());
		return performance;
	}

	/**
	 * Flushes the internal buffered log messages to a file on the desktop.
	 */
	private void flushLogToFile() {
		// If logging directory does not exist, try to create it
		if (!LOG_PATH.exists()) {
			LOG_PATH.mkdir();
		}

		PrintWriter writer = null;

		File dataFile = null;
		boolean foundSmallLogFile = false;
		int highestLogFileIndex = 0;
		for (final File logFile : LOG_PATH.listFiles(mLogFileFilter)) {
			if (logFile.length() < LOG_FILE_SIZE_THRESHOLD) {
				foundSmallLogFile = true;
				dataFile = logFile;
				break;
			}
			// Get the index of this log file
			final String name = logFile.getName();
			final int index =
					Integer.parseInt(name.replaceFirst(LOG_PATH_DATA, "").replaceFirst(LOG_PATH_DATA_EXT, ""));
			if (index > highestLogFileIndex) {
				highestLogFileIndex = index;
			}
		}
		if (!foundSmallLogFile) {
			highestLogFileIndex++;
			dataFile = new File(LOG_PATH, LOG_PATH_DATA + highestLogFileIndex + LOG_PATH_DATA_EXT);
		}

		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(dataFile, true)));
			for (final String message : mLoggedLines) {
				writer.println(message);
			}
		} catch (final IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
		mLogger.info("Logged data to file (" + dataFile.getAbsolutePath() + ").");
	}

	/**
	 * Flushes the internal buffered log messages to the used logger.
	 */
	@SuppressWarnings("unused")
	private void flushLogToLogger() {
		for (final String message : mLoggedLines) {
			mLogger.info(message);
		}
	}

	/**
	 * Logs a given message as single line. Uses a internal buffer that needs to be flushed in order to actually print
	 * the logs. Flushing is done by using {@link #flushLogToLogger()}.
	 *
	 * @param message
	 *            Message to log
	 */
	private void logLine(final String message) {
		mLoggedLines.add(message);
	}

	/**
	 * Saves the state of a given performance in internal fields.
	 *
	 * @param performance
	 *            Performance to save
	 */
	private void saveStateOfPerformance(final SimulationPerformance performance) {
		for (final TimeMeasure measure : mTimeMeasures.keySet()) {
			final long durationInMillis = performance.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);
			if (durationInMillis == SimulationPerformance.NO_TIME_RESULT) {
				mTimeMeasures.put(measure, (float) SimulationPerformance.NO_TIME_RESULT);
			} else {
				mTimeMeasures.put(measure, ComparisonTables.millisToSeconds(durationInMillis));
			}
		}
		for (final CountingMeasure measure : mCountingMeasures.keySet()) {
			final int counter = performance.getCountingMeasureResult(measure);
			mCountingMeasures.put(measure, counter);
		}
	}

	/**
	 * Adds general automata performance data for external methods to the internal measure structures.
	 *
	 * @param input
	 *            Input automaton before using the external method
	 * @param output
	 *            Output automaton after using the external method
	 */
	protected void addGeneralAutomataPerformanceForExternalMethod(final INestedWordAutomaton<LETTER, STATE> input,
			final INestedWordAutomaton<LETTER, STATE> output) {
		final AutomataLibraryServices services = getServices();

		// Input automaton
		final Analyze<LETTER, STATE> inputAnalyzer = new Analyze<>(services, input, true);
		final int inputStates = inputAnalyzer.getNumberOfStates();
		final int inputTransitions = inputAnalyzer.getNumberOfTransitions(SymbolType.TOTAL);
		mCountingMeasures.put(CountingMeasure.BUCHI_STATES, inputStates);
		mCountingMeasures.put(CountingMeasure.BUCHI_NONDETERMINISTIC_STATES,
				inputAnalyzer.getNumberOfNondeterministicStates());

		mCountingMeasures.put(CountingMeasure.BUCHI_ALPHABET_SIZE, inputAnalyzer.getNumberOfSymbols(SymbolType.TOTAL));
		mCountingMeasures.put(CountingMeasure.BUCHI_TRANSITIONS, inputTransitions);
		mCountingMeasures.put(CountingMeasure.BUCHI_TRANSITION_DENSITY_MILLION,
				(int) Math.round(inputAnalyzer.getTransitionDensity(SymbolType.TOTAL) * 1_000_000));

		// Output automaton
		if (output != null) {
			final Analyze<LETTER, STATE> outputAnalyzer = new Analyze<>(services, output, true);
			final int outputStates = outputAnalyzer.getNumberOfStates();
			final int outputTransitions = outputAnalyzer.getNumberOfTransitions(SymbolType.TOTAL);
			mCountingMeasures.put(CountingMeasure.RESULT_STATES, outputStates);
			mCountingMeasures.put(CountingMeasure.RESULT_NONDETERMINISTIC_STATES,
					outputAnalyzer.getNumberOfNondeterministicStates());

			mCountingMeasures.put(CountingMeasure.RESULT_ALPHABET_SIZE,
					outputAnalyzer.getNumberOfSymbols(SymbolType.TOTAL));
			mCountingMeasures.put(CountingMeasure.RESULT_TRANSITIONS, outputTransitions);
			mCountingMeasures.put(CountingMeasure.RESULT_TRANSITION_DENSITY_MILLION,
					(int) Math.round(outputAnalyzer.getTransitionDensity(SymbolType.TOTAL) * 1_000_000));

			// General metrics
			mCountingMeasures.put(CountingMeasure.REMOVED_STATES, inputStates - outputStates);
			mCountingMeasures.put(CountingMeasure.REMOVED_TRANSITIONS, inputTransitions - outputTransitions);
		}
	}

	/**
	 * Measures the effectiveness of a given method for buechi reduction and logs it.
	 *
	 * @param method
	 *            Used method
	 * @param name
	 *            Name of the automaton used for the method
	 * @param type
	 *            The type of the used simulation
	 * @param usedSCCs
	 *            If the method used SCCs
	 * @param timedOut
	 *            If the method timed out or not
	 * @param outOfMemory
	 *            If the method has thrown an out of memory error
	 * @param operand
	 *            The automaton the method processed
	 */
	@SuppressWarnings("unchecked")
	protected void appendMethodPerformanceToLog(final Object method, final String name,
			final SimulationOrMinimizationType type, final boolean usedSCCs, final boolean timedOut,
			final boolean outOfMemory, final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand) {
		createAndResetPerformanceHead();

		if (method instanceof ASimulation) {
			final ASimulation<LETTER, STATE> simulation = (ASimulation<LETTER, STATE>) method;
			final SimulationPerformance performance = simulation.getSimulationPerformance();

			if (timedOut) {
				performance.timeOut();
			}
			if (outOfMemory) {
				performance.outOfMemory();
			}
			performance.setName(name);
			saveStateOfPerformance(performance);
		} else if (method instanceof ReduceNwaFullMultipebbleSimulation) {
			final ReduceNwaFullMultipebbleSimulation<LETTER, STATE, FullMultipebbleGameState<STATE>> fullMultipebbleSimulation =
					(ReduceNwaFullMultipebbleSimulation<LETTER, STATE, FullMultipebbleGameState<STATE>>) method;
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> methodResult = fullMultipebbleSimulation.getResult();
			// Performance data
			addGeneralAutomataPerformanceForExternalMethod((INestedWordAutomaton<LETTER, STATE>) operand,
					(INestedWordAutomaton<LETTER, STATE>) methodResult);
			// Overall time
			mTimeMeasures.put(TimeMeasure.OVERALL, ComparisonTables.millisToSeconds(mExternalOverallTime));
		} else if (method instanceof MinimizeSevpa) {
			final MinimizeSevpa<LETTER, STATE> minimizeSevpa = (MinimizeSevpa<LETTER, STATE>) method;
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> methodResult = minimizeSevpa.getResult();
			// Performance data
			addGeneralAutomataPerformanceForExternalMethod((INestedWordAutomaton<LETTER, STATE>) operand,
					(INestedWordAutomaton<LETTER, STATE>) methodResult);
			// Overall time
			mTimeMeasures.put(TimeMeasure.OVERALL, ComparisonTables.millisToSeconds(mExternalOverallTime));
		} else if (method instanceof ShrinkNwa) {
			final ShrinkNwa<LETTER, STATE> shrinkNwa = (ShrinkNwa<LETTER, STATE>) method;
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> methodResult = shrinkNwa.getResult();
			// Performance data
			addGeneralAutomataPerformanceForExternalMethod((INestedWordAutomaton<LETTER, STATE>) operand,
					(INestedWordAutomaton<LETTER, STATE>) methodResult);
			// Overall time
			mTimeMeasures.put(TimeMeasure.OVERALL, ComparisonTables.millisToSeconds(mExternalOverallTime));
		} else if (method instanceof MinimizeNwaPmaxSat) {
			final MinimizeNwaPmaxSat<LETTER, STATE> minimizeNwaPmaxSat = (MinimizeNwaPmaxSat<LETTER, STATE>) method;
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> methodResult = minimizeNwaPmaxSat.getResult();
			// Performance data
			addGeneralAutomataPerformanceForExternalMethod((INestedWordAutomaton<LETTER, STATE>) operand,
					(INestedWordAutomaton<LETTER, STATE>) methodResult);
			// Overall time
			mTimeMeasures.put(TimeMeasure.OVERALL, ComparisonTables.millisToSeconds(mExternalOverallTime));
		}

		if (timedOut && method == null) {
			saveStateOfPerformance(createTimedOutPerformance(name, type, usedSCCs, operand));
		} else if (outOfMemory && method == null) {
			saveStateOfPerformance(createOutOfMemoryPerformance(name, type, usedSCCs, operand));
		}

		appendCurrentPerformanceEntryToLog(name, type, usedSCCs, timedOut, outOfMemory);
	}

	/**
	 * Gets the logger object used by this operation.
	 *
	 * @return The logger object used by this operation.
	 */
	protected ILogger getLogger() {
		return mLogger;
	}

	@Override
	protected INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getOperand() {
		return mOperand;
	}

	/**
	 * Gets the service object used by this operation.
	 *
	 * @return The service object used by this operation.
	 */
	protected AutomataLibraryServices getServices() {
		return mServices;
	}

	/**
	 * Measures the performance of a simulation, represented by a given type, on a given automaton and appends its
	 * performance to the log.
	 *
	 * @param name
	 *            Name of the automaton used for the simulation method
	 * @param type
	 *            Type of the simulation method to measure performance for
	 * @param useSCCs
	 *            If the simulation should use SCCs
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param timeout
	 *            A time duration, in milliseconds, after which the method should automatically timeout and abort.
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 */
	protected void measureMethodPerformance(final String name, final SimulationOrMinimizationType type,
			final boolean useSCCs, final AutomataLibraryServices services, final long timeout,
			final IMinimizationStateFactory<STATE> stateFactory, final INestedWordAutomaton<LETTER, STATE> operand) {
		final IProgressAwareTimer progressTimer = services.getProgressAwareTimer().getChildTimer(timeout);
		boolean timedOut = false;
		boolean outOfMemory = false;
		Object method = null;

		try {
			if (type.equals(SimulationOrMinimizationType.DIRECT)) {
				final DirectGameGraph<LETTER, STATE> graph =
						new DirectGameGraph<>(services, stateFactory, progressTimer, mLogger, operand);
				graph.generateGameGraphFromAutomaton();
				final DirectSimulation<LETTER, STATE> sim =
						new DirectSimulation<>(progressTimer, mLogger, useSCCs, stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(SimulationOrMinimizationType.DELAYED)) {
				final DelayedGameGraph<LETTER, STATE> graph =
						new DelayedGameGraph<>(services, stateFactory, progressTimer, mLogger, operand);
				graph.generateGameGraphFromAutomaton();
				final DelayedSimulation<LETTER, STATE> sim =
						new DelayedSimulation<>(progressTimer, mLogger, useSCCs, stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(SimulationOrMinimizationType.FAIR)) {
				final FairGameGraph<LETTER, STATE> graph =
						new FairGameGraph<>(services, stateFactory, progressTimer, mLogger, operand);
				graph.generateGameGraphFromAutomaton();
				final FairSimulation<LETTER, STATE> sim =
						new FairSimulation<>(progressTimer, mLogger, useSCCs, stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(SimulationOrMinimizationType.FAIRDIRECT)) {
				final FairDirectGameGraph<LETTER, STATE> graph =
						new FairDirectGameGraph<>(services, stateFactory, progressTimer, mLogger, operand);
				graph.generateGameGraphFromAutomaton();
				final FairDirectSimulation<LETTER, STATE> sim =
						new FairDirectSimulation<>(progressTimer, mLogger, useSCCs, stateFactory, graph);
				sim.doSimulation();
				method = sim;
			} else if (type.equals(SimulationOrMinimizationType.EXT_MINIMIZESEVPA)) {
				final long startTime = System.currentTimeMillis();
				method = new MinimizeSevpa<>(mServices, stateFactory, operand);
				mExternalOverallTime = System.currentTimeMillis() - startTime;
			} else if (type.equals(SimulationOrMinimizationType.EXT_SHRINKNWA)) {
				final long startTime = System.currentTimeMillis();
				method = new ShrinkNwa<>(mServices, stateFactory, operand);
				mExternalOverallTime = System.currentTimeMillis() - startTime;
			} else if (type.equals(SimulationOrMinimizationType.EXT_MINIMIZENWAMAXSAT)) {
				IDoubleDeckerAutomaton<LETTER, STATE> operandAsNwa = null;
				if (operand instanceof IDoubleDeckerAutomaton<?, ?>) {
					operandAsNwa = (IDoubleDeckerAutomaton<LETTER, STATE>) operand;
				} else {
					operandAsNwa = new RemoveUnreachable<>(services, operand).getResult();
				}
				final long startTime = System.currentTimeMillis();
				method = new MinimizeNwaPmaxSatDirect<>(mServices, stateFactory, operandAsNwa);
				mExternalOverallTime = System.currentTimeMillis() - startTime;
			}
		} catch (final AutomataOperationCanceledException e) {
			mLogger.info("Method timed out.");
			timedOut = true;
		} catch (final OutOfMemoryError e) {
			mLogger.info("Method has thrown an out of memory error.");
			outOfMemory = true;
		}
		appendMethodPerformanceToLog(method, name, type, useSCCs, timedOut, outOfMemory, operand);
	}

	/**
	 * Starts measuring performances for all simulation methods to compare.
	 *
	 * @param automatonName
	 *            Name of the operand automaton to measure performance for
	 * @param timeOutMillis
	 *            Time out in milliseconds each method has
	 * @param stateFactory
	 *            Factory used to create states
	 * @param reachableOperand
	 *            Operand where non reachable states are removed
	 */
	protected void measurePerformances(final String automatonName, final long timeOutMillis,
			final IMinimizationStateFactory<STATE> stateFactory,
			final NestedWordAutomatonReachableStates<LETTER, STATE> reachableOperand) {
		// Direct simulation without SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.DIRECT, false, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Direct simulation with SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.DIRECT, true, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Delayed simulation without SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.DELAYED, false, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Delayed simulation with SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.DELAYED, true, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Fair simulation without SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.FAIR, false, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Fair simulation with SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.FAIR, true, mServices, timeOutMillis,
				stateFactory, reachableOperand);
		// Fair direct simulation without SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.FAIRDIRECT, false, mServices,
				timeOutMillis, stateFactory, reachableOperand);
		// Fair direct simulation with SCC
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.FAIRDIRECT, true, mServices, timeOutMillis,
				stateFactory, reachableOperand);

		// Other minimization methods
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.EXT_MINIMIZESEVPA, true, mServices,
				timeOutMillis, stateFactory, reachableOperand);
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.EXT_SHRINKNWA, true, mServices,
				timeOutMillis, stateFactory, reachableOperand);
		measureMethodPerformance(automatonName, SimulationOrMinimizationType.EXT_MINIMIZENWAMAXSAT, true, mServices,
				timeOutMillis, stateFactory, reachableOperand);
	}

	/**
	 * Sets the value for the overall time an external method needed.
	 *
	 * @param time
	 *            Time to set
	 */
	protected void setExternalOverallTime(final long time) {
		mExternalOverallTime = time;
	}

	/**
	 * Reads the log file and creates readable performance tables as html files.
	 *
	 * @param args
	 *            Not supported
	 */
	public static void main(final String[] args) {
		System.out.println("Parsing log file...");
		final LinkedList<LinkedList<SimulationPerformance>> performanceEntries = parseLogFile();

		System.out.println("Processing data...");
		final List<Pair<String, List<String>>> tables = new LinkedList<>();
		tables.add(new Pair<>("instanceFullComparison", ComparisonTables
				.createInstanceFullComparisonTable(performanceEntries, LOG_SEPARATOR, null, false, false, true)));
		// tables.add(new Pair<>("instanceTimePartitioning",
		// ComparisonTables.createInstanceTimePartitioningTable(performanceEntries, LOG_SEPARATOR)));
		// tables.add(new Pair<>("instanceAlgoWork",
		// ComparisonTables.createInstanceAlgoWorkTable(performanceEntries, LOG_SEPARATOR)));
		// tables.add(new Pair<>("averagedSimulationFullComparison",
		// ComparisonTables.createAveragedSimulationFullComparisonTable(performanceEntries, LOG_SEPARATOR, null, false,
		// false, true)));
		tables.add(new Pair<>("averagedSimulationPerDirectoryTable",
				ComparisonTables.createAveragedSimulationPerDirectoryTable(performanceEntries, LOG_SEPARATOR,
						SimulationOrMinimizationType.EXT_RABIT_LIGHT_1, false, false, true)));
		// tables.add(new Pair<>("averagedSimulationTimePartitioning",
		// ComparisonTables.createAveragedSimulationTimePartitioningTable(performanceEntries, LOG_SEPARATOR)));
		// tables.add(new Pair<>("averagedSimulationAlgoWork",
		// ComparisonTables.createAveragedSimulationAlgoWorkTable(performanceEntries, LOG_SEPARATOR)));
		// tables.add(new Pair<>("timedOutNames", ComparisonTables.createTimedOutNamesTable(performanceEntries)));
		// tables.add(new Pair<>("noRemoveNames", ComparisonTables.createNoRemoveNamesTable(performanceEntries)));
		// tables.add(new Pair<>("smallSizeNames", ComparisonTables.createSmallSizeNamesTable(performanceEntries)));
		// tables.add(new Pair<>("longerThanOneSecondNames",
		// ComparisonTables.createLongerThanOneSecondNamesTable(performanceEntries)));

		// tables.add(new Pair<>("directFilteredInstanceFullComparison",
		// ComparisonTables.createInstanceFullComparisonTable(performanceEntries, LOG_SEPARATOR, ESimulationType.DIRECT,
		// true, true, true)));
		// tables.add(new Pair<>("delayedFilteredInstanceFullComparison",
		// ComparisonTables.createInstanceFullComparisonTable(performanceEntries, LOG_SEPARATOR,
		// ESimulationType.DELAYED, true, true, true)));
		// tables.add(new Pair<>("directFilteredAverageFullComparison",
		// ComparisonTables.createAveragedSimulationFullComparisonTable(performanceEntries, LOG_SEPARATOR,
		// ESimulationType.DIRECT, true, true, true)));
		// tables.add(new Pair<>("delayedFilteredAverageFullComparison",
		// ComparisonTables.createAveragedSimulationFullComparisonTable(performanceEntries, LOG_SEPARATOR,
		// ESimulationType.DELAYED, true, true, true)));

		System.out.println("Creating html files...");
		for (final Pair<String, List<String>> pair : tables) {
			tableToHtmlFile(pair.getFirst(), pair.getSecond());
		}

		System.out.println("Creating plot files...");
		for (final Pair<String, List<String>> pair : tables) {
			tableToPlotFile(pair.getFirst(), pair.getSecond());
		}

		System.out.println("Terminated.");
	}

	/**
	 * Parses the file {@link #LOG_PATH_DATA} and sets a data structure up which holds all data from the log file.
	 *
	 * @return A data structure holding all data from the log file.
	 */
	@SuppressWarnings("unchecked")
	private static LinkedList<LinkedList<SimulationPerformance>> parseLogFile() {
		BufferedReader br = null;
		try {
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries = new LinkedList<>();
			LinkedList<SimulationPerformance> currentPerformanceEntry = null;
			final ArrayList<TimeMeasure> currentTimeMeasures = new ArrayList<>();
			final ArrayList<CountingMeasure> currentCountingMeasures = new ArrayList<>();

			// Setup isValidEnum - Map
			final HashMap<String, TimeMeasure> nameToTimeMeasure = new HashMap<>();
			for (final TimeMeasure measure : TimeMeasure.values()) {
				nameToTimeMeasure.put(measure.name(), measure);
			}
			final HashMap<String, CountingMeasure> nameToCountingMeasure = new HashMap<>();
			for (final CountingMeasure measure : CountingMeasure.values()) {
				nameToCountingMeasure.put(measure.name(), measure);
			}

			final FileFilter logFileFilter = new FileFilter() {
				/*
				 * (non-Javadoc)
				 *
				 * @see java.io.FileFilter#accept(java.io.File)
				 */
				@Override
				public boolean accept(final File pathname) {
					final String name = pathname.getName();
					return name.startsWith(LOG_PATH_DATA) && name.endsWith(LOG_PATH_DATA_EXT);
				}
			};
			for (final File logFile : LOG_PATH.listFiles(logFileFilter)) {
				br = new BufferedReader(new FileReader(logFile));
				while (br.ready()) {
					final String line = br.readLine();

					final String[] lineElements = line.split(LOG_SEPARATOR);
					if (lineElements[0].startsWith(LOG_ENTRY_HEAD_START)) {
						// Line marks start of a head entry

						// Save last entry before starting a new one
						if (currentPerformanceEntry != null && !currentPerformanceEntry.isEmpty()) {
							performanceEntries.add((LinkedList<SimulationPerformance>) currentPerformanceEntry.clone());
						}

						// Start a new entry
						currentPerformanceEntry = new LinkedList<>();
						currentTimeMeasures.clear();
						currentCountingMeasures.clear();

						// Parse the current header and the order of measures
						for (int i = FIX_FIELD_AMOUNT + 1; i < lineElements.length; i++) {
							// End if end of the head entry is reached
							final String measureName = lineElements[i];
							if (measureName.equals(LOG_ENTRY_HEAD_END)) {
								break;
							}
							if (nameToTimeMeasure.containsKey(measureName)) {
								currentTimeMeasures.add(nameToTimeMeasure.get(measureName));
							} else if (nameToCountingMeasure.containsKey(measureName)) {
								currentCountingMeasures.add(nameToCountingMeasure.get(measureName));
							}
						}
					} else {
						// Line is a data set of the current performance entry
						// Fix fields
						final String name = lineElements[0];
						final SimulationOrMinimizationType type = SimulationOrMinimizationType.valueOf(lineElements[1]);
						final boolean usedSCCs = Boolean.parseBoolean(lineElements[2]);
						final boolean timedOut = Boolean.parseBoolean(lineElements[3]);
						final boolean outOfMemory = Boolean.parseBoolean(lineElements[4]);
						final SimulationPerformance performance = new SimulationPerformance(type, usedSCCs);
						if (timedOut) {
							performance.timeOut();
						}
						if (outOfMemory) {
							performance.outOfMemory();
						}
						performance.setName(name);

						// Parse the rest of the data set
						for (int i = FIX_FIELD_AMOUNT; i < lineElements.length; i++) {
							final int indexTimeMeasure = i - FIX_FIELD_AMOUNT;
							final int indexCountingMeasure = i - FIX_FIELD_AMOUNT - currentTimeMeasures.size();
							if (indexTimeMeasure >= 0 && indexTimeMeasure < currentTimeMeasures.size()) {
								final TimeMeasure measure = currentTimeMeasures.get(indexTimeMeasure);
								final float value = Float.parseFloat(lineElements[i]);
								if (value == SimulationPerformance.NO_TIME_RESULT) {
									performance.addTimeMeasureValue(measure, SimulationPerformance.NO_TIME_RESULT);
								} else {
									performance.addTimeMeasureValue(measure, ComparisonTables.secondsToMillis(value));
								}
							} else if (indexCountingMeasure >= 0
									&& indexCountingMeasure < currentCountingMeasures.size()) {
								final CountingMeasure measure = currentCountingMeasures.get(indexCountingMeasure);
								final int value = Integer.parseInt(lineElements[i]);
								if (value == SimulationPerformance.NO_COUNTING_RESULT) {
									performance.setCountingMeasure(measure, SimulationPerformance.NO_COUNTING_RESULT);
								} else {
									performance.setCountingMeasure(measure, value);
								}
							}
						}

						// Put the data in the element
						currentPerformanceEntry.add(performance);
					}
				}
				// Save last entry
				if (currentPerformanceEntry != null && !currentPerformanceEntry.isEmpty()) {
					performanceEntries.add(currentPerformanceEntry);
				}
			}

			return performanceEntries;
		} catch (final IOException e) {
			e.printStackTrace();
		} finally {
			if (br != null) {
				try {
					br.close();
				} catch (final IOException e) {
					e.printStackTrace();
				}
			}
		}

		return null;
	}

	/**
	 * Parses a table, in a format like .csv or .tsv where {@link #LOG_SEPARATOR} is the separator. The parsed table
	 * then is written to a html-file on the desktop.
	 *
	 * @param name
	 *            Name for the html file
	 * @param table
	 *            Table to convert
	 */
	private static void tableToHtmlFile(final String name, final List<String> table) {
		final StringBuilder htmlText = new StringBuilder();
		final String normalCellTag = "td";
		final String headerCellTag = "th";

		htmlText.append("<!DOCTYPE html><html><head>");
		htmlText.append("<title>Simulation Performance Test-Results</title>");

		// JS
		htmlText.append(
				"<script type=\"text/javascript\" src=\"https://ajax.googleapis.com/ajax/libs/jquery/3.1.0/jquery.min.js\"></script>");
		htmlText.append("<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/sorttable.js\"></script>");
		htmlText.append("<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/markRows.js\"></script>");
		htmlText.append(
				"<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/toggleEmptyColumns.js\"></script>");

		// CSS
		htmlText.append("<style>");
		// Wikitable classes
		htmlText.append("table.wikitable { margin: 1em 0; background-color: #f9f9f9;"
				+ " border: 1px solid #aaa;border-collapse: collapse; color: black }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > tr > td,"
				+ " table.wikitable > * > tr > th, table.wikitable > * > tr > td {"
				+ " border: 1px solid #aaa; padding: 0.2em 0.4em }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > * > tr > th {"
				+ " background-color: #f2f2f2; text-align: center }");
		htmlText.append("table.wikitable > caption { font-weight: bold }");
		// Alternating row coloring
		htmlText.append("tr:nth-child(even) { background-color: #f9f9f9 }");
		htmlText.append("tr:nth-child(odd) { background-color: #e9e9e9 }");
		// Empty row highlighting
		htmlText.append(".emptyrow { background-color: #c9c9c9 !important; }");
		// Sortable icons
		htmlText.append("table.sortable th:not(.sorttable_sorted):not(.sorttable_sorted_reverse)"
				+ ":not(.sorttable_nosort):after { content: \" \\25B4\\25BE\"; }");
		// Mark rows
		htmlText.append("#markRowText { margin-left: 1em; }");
		htmlText.append(".markedRow { background-color: #FFB0B0 !important; }");
		// Toggle empty columns
		htmlText.append(".cellOfEmptyColumn { display: none; }");
		htmlText.append("#toggleEmptyColumnsButton { margin-left: 1em; }");
		htmlText.append("</style>");

		htmlText.append("</head><body>");
		htmlText.append(
				"<span class=\"markedRow demoText\">Mark rows:</span><input type=\"text\" id=\"markRowText\" name=\"markRowText\" oninput=\"markRows()\" />");
		htmlText.append(
				"<button type=\"button\" id=\"toggleEmptyColumnsButton\" onclick=\"toggleEmptyColumns()\">Hide/Show empty columns</button>");
		htmlText.append("<br/>");
		htmlText.append("<table id=\"contentTable\" class=\"wikitable sortable\">");

		boolean isFirstRow = true;
		for (final String row : table) {
			// First row is header
			String cellTag = normalCellTag;
			if (isFirstRow) {
				cellTag = headerCellTag;
			}

			// Empty row
			if (row.isEmpty()) {
				htmlText.append(
						"<tr class=\"emptyrow\"><td colspan=\"100%\">&nbsp;</td></tr>" + System.lineSeparator());
				continue;
			}

			// Row is not empty
			final String[] cells = row.split(LOG_SEPARATOR);
			if (cells.length > 0) {
				htmlText.append("<tr>");
				for (final String value : cells) {
					String valueText = value;
					if (value.equals(ComparisonTables.NO_VALUE)) {
						valueText = HTML_NO_VALUE;
					}
					htmlText.append("<" + cellTag + ">" + valueText + "</" + cellTag + ">");
				}
				htmlText.append("</tr>" + System.lineSeparator());
			}

			isFirstRow = false;
		}
		htmlText.append("</table></body></html>");

		// Write html to file
		PrintWriter writer = null;
		final File resultFile = new File(LOG_PATH, LOG_PATH_HTML_PRE + name + LOG_PATH_HTML_SUFF);
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(resultFile)));
			writer.print(htmlText.toString());
		} catch (final IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
	}

	/**
	 * Parses a table, in a format like .csv or .tsv where {@link #LOG_SEPARATOR} is the separator. The parsed table
	 * then is written to a plot-able csv-file on the desktop.
	 *
	 * @param name
	 *            Name for the csv file
	 * @param table
	 *            Table to convert
	 */
	private static void tableToPlotFile(final String name, final List<String> table) {
		final StringBuilder tsvText = new StringBuilder();
		for (final String row : table) {
			// Empty row
			if (row.isEmpty()) {
				tsvText.append(System.lineSeparator());
				continue;
			}

			// Row is not empty
			final String[] cells = row.split(LOG_SEPARATOR);
			if (cells.length > 0) {
				boolean isFirstCell = true;
				for (final String value : cells) {
					if (isFirstCell) {
						isFirstCell = false;
					} else {
						tsvText.append(PLOT_SEPARATOR);
					}
					String valueText = value;
					if (value.equals(ComparisonTables.NO_VALUE)) {
						valueText = PLOT_NO_VALUE;
					}
					tsvText.append(valueText);
				}
				tsvText.append(System.lineSeparator());
			}
		}

		// Write tsv to file
		PrintWriter writer = null;
		final File resultFile = new File(LOG_PATH, LOG_PATH_PLOT_PRE + name + LOG_PATH_PLOT_SUFF);
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(resultFile)));
			writer.print(tsvText.toString());
		} catch (final IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
	}
}
