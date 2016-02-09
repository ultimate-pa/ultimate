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

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedList;
import java.util.List;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveNonLiveStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.RemoveUnreachable;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.delayed.DelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.util.relation.Pair;

/**
 * Operation that compares the different types of simulation methods for buechi
 * reduction.<br/>
 * The resulting automaton is the input automaton.
 * 
 * @author Daniel Tischner
 * 
 * @param <LETTER>
 *            Letter class of buechi automaton
 * @param <STATE>
 *            State class of buechi automaton
 */
public final class CompareReduceBuchiSimulation<LETTER, STATE> implements IOperation<LETTER, STATE> {

	/**
	 * Amount of fix fields in the log format. Currently this is name, type,
	 * usedSCCs, timedOut and outOfMemory.
	 */
	private final static int FIX_FIELD_AMOUNT = 5;
	/**
	 * Marks the end of the head from an entry.
	 */
	private final static String LOG_ENTRY_HEAD_END = "-->";
	/**
	 * Marks the start of the head from an entry.
	 */
	private final static String LOG_ENTRY_HEAD_START = "<!--";
	/**
	 * Path where simulation perfomance relevant logs and data gets saved.
	 */
	private static final File LOG_PATH = new File(new File(System.getProperty("user.home"), "Desktop"),
			"simulationPerformance");
	/**
	 * Name for the object of the log file.
	 */
	private static final String LOG_PATH_DATA = "testData.tsv";
	/**
	 * Prefix for test result files.
	 */
	private static final String LOG_PATH_HTML_PRE = "testResults_";
	/**
	 * Suffix for test result files.
	 */
	private static final String LOG_PATH_HTML_SUFF = ".html";
	/**
	 * Separator that is used in the log.
	 */
	private final static String LOG_SEPARATOR = "\t";
	/**
	 * Time in seconds after which a simulation method should timeout.
	 */
	private final static int SIMULATION_TIMEOUT = 10;

	/**
	 * Reads the log file and creates readable performance tables as html files.
	 * 
	 * @param args
	 *            Not supported
	 */
	public static void main(final String[] args) {
		System.out.println("Parsing log file...");
		LinkedList<LinkedList<SimulationPerformance>> performanceEntries = parseLogFile();

		System.out.println("Processing data...");
		List<Pair<String, List<String>>> tables = new LinkedList<>();
		tables.add(new Pair<>("instanceFullComparison",
				ComparisonTables.createInstanceFullComparisonTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("instanceTimePartitioning",
				ComparisonTables.createInstanceTimePartitioningTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("instanceAlgoWork",
				ComparisonTables.createInstanceAlgoWorkTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("averagedSimulationFullComparison",
				ComparisonTables.createAveragedSimulationFullComparisonTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("averagedSimulationTimePartitioning",
				ComparisonTables.createAveragedSimulationTimePartitioningTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("averagedSimulationAlgoWork",
				ComparisonTables.createAveragedSimulationAlgoWorkTable(performanceEntries, LOG_SEPARATOR)));
		tables.add(new Pair<>("timedOutNames", ComparisonTables.createTimedOutNamesTable(performanceEntries)));
		tables.add(new Pair<>("noRemoveNames", ComparisonTables.createNoRemoveNamesTable(performanceEntries)));
		tables.add(new Pair<>("smallSizeNames", ComparisonTables.createSmallSizeNamesTable(performanceEntries)));

		System.out.println("Creating html files...");
		for (Pair<String, List<String>> pair : tables) {
			tableToHtmlFile(pair.getFirst(), pair.getSecond());
		}

		System.out.println("Terminated.");
	}

	/**
	 * Parses the file {@link #LOG_PATH_DATA} and sets a data structure up which
	 * holds all data from the log file.
	 * 
	 * @return A data structure holding all data from the log file.
	 */
	@SuppressWarnings("unchecked")
	private static LinkedList<LinkedList<SimulationPerformance>> parseLogFile() {
		BufferedReader br = null;
		try {
			LinkedList<LinkedList<SimulationPerformance>> performanceEntries = new LinkedList<>();
			LinkedList<SimulationPerformance> currentPerformanceEntry = null;
			ArrayList<ETimeMeasure> currentTimeMeasures = new ArrayList<>();
			ArrayList<ECountingMeasure> currentCountingMeasures = new ArrayList<>();

			// Setup isValidEnum - Map
			HashMap<String, ETimeMeasure> nameToTimeMeasure = new HashMap<>();
			for (ETimeMeasure measure : ETimeMeasure.values()) {
				nameToTimeMeasure.put(measure.name(), measure);
			}
			HashMap<String, ECountingMeasure> nameToCountingMeasure = new HashMap<>();
			for (ECountingMeasure measure : ECountingMeasure.values()) {
				nameToCountingMeasure.put(measure.name(), measure);
			}

			br = new BufferedReader(new FileReader(new File(LOG_PATH, LOG_PATH_DATA)));
			while (br.ready()) {
				String line = br.readLine();

				String[] lineElements = line.split(LOG_SEPARATOR);
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
						String measureName = lineElements[i];
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
					String name = lineElements[0];
					ESimulationType type = ESimulationType.valueOf(lineElements[1]);
					boolean usedSCCs = Boolean.parseBoolean(lineElements[2]);
					boolean timedOut = Boolean.parseBoolean(lineElements[3]);
					boolean outOfMemory = Boolean.parseBoolean(lineElements[4]);
					SimulationPerformance performance = new SimulationPerformance(type, usedSCCs);
					if (timedOut) {
						performance.timeOut();
					}
					if (outOfMemory) {
						performance.outOfMemory();
					}
					performance.setName(name);

					// Parse the rest of the data set
					for (int i = FIX_FIELD_AMOUNT; i < lineElements.length; i++) {
						int indexTimeMeasure = i - FIX_FIELD_AMOUNT;
						int indexCountingMeasure = i - FIX_FIELD_AMOUNT - currentTimeMeasures.size();
						if (indexTimeMeasure >= 0 && indexTimeMeasure < currentTimeMeasures.size()) {
							ETimeMeasure measure = currentTimeMeasures.get(indexTimeMeasure);
							float value = Float.parseFloat(lineElements[i]);
							if (value == SimulationPerformance.NO_TIME_RESULT) {
								performance.addTimeMeasureValue(measure, SimulationPerformance.NO_TIME_RESULT);
							} else {
								performance.addTimeMeasureValue(measure, ComparisonTables.secondsToMillis(value));
							}
						} else if (indexCountingMeasure >= 0 && indexCountingMeasure < currentCountingMeasures.size()) {
							ECountingMeasure measure = currentCountingMeasures.get(indexCountingMeasure);
							int value = Integer.parseInt(lineElements[i]);
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

			return performanceEntries;
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (br != null) {
				try {
					br.close();
				} catch (IOException e) {
					e.printStackTrace();
				}
			}
		}

		return null;
	}

	/**
	 * Parses a table, in a format like .csv or .tsv where
	 * {@link #LOG_SEPARATOR} is the separator. The parsed table then is writen
	 * to a html-file on the desktop.
	 * 
	 * @param name
	 *            Name for the html file
	 * @param table
	 *            Table to convert
	 */
	private static void tableToHtmlFile(final String name, final List<String> table) {
		StringBuilder htmlText = new StringBuilder();
		String normalCellTag = "td";
		String headerCellTag = "th";

		htmlText.append("<!DOCTYPE html><html><head>");
		htmlText.append("<title>Simulation Performance Test-Results</title>");

		// JS
		htmlText.append("<script type=\"text/javascript\" src=\"http://zabuza.square7.ch/sorttable.js\"></script>");

		// CSS
		htmlText.append("<style>");
		// Wikitable class
		htmlText.append("table.wikitable { margin: 1em 0; background-color: #f9f9f9;"
				+ " border: 1px solid #aaa;border-collapse: collapse; color: black }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > tr > td,"
				+ " table.wikitable > * > tr > th, table.wikitable > * > tr > td {"
				+ " border: 1px solid #aaa; padding: 0.2em 0.4em }");
		htmlText.append("table.wikitable > tr > th, table.wikitable > * > tr > th {"
				+ " background-color: #f2f2f2; text-align: center }");
		htmlText.append("table.wikitable > caption { font-weight: bold }");
		// Other classes
		htmlText.append("tr:nth-child(even) { background-color: #f9f9f9 }");
		htmlText.append("tr:nth-child(odd) { background-color: #e9e9e9 }");
		htmlText.append(".emptyrow { background-color: #c9c9c9 !important; }");
		htmlText.append("table.sortable th:not(.sorttable_sorted):not(.sorttable_sorted_reverse)"
				+ ":not(.sorttable_nosort):after { content: \" \\25B4\\25BE\"; }");
		htmlText.append("</style>");

		htmlText.append("</head><body><table class=\"wikitable sortable\">");
		boolean isFirstRow = true;
		for (String row : table) {
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
			String[] cells = row.split(LOG_SEPARATOR);
			if (cells.length > 0) {
				htmlText.append("<tr>");
				for (String value : cells) {
					htmlText.append("<" + cellTag + ">" + value + "</" + cellTag + ">");
				}
				htmlText.append("</tr>" + System.lineSeparator());
			}

			isFirstRow = false;
		}
		htmlText.append("</table></body></html>");

		// Write html to file
		PrintWriter writer = null;
		File resultFile = new File(LOG_PATH, LOG_PATH_HTML_PRE + name + LOG_PATH_HTML_SUFF);
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(resultFile)));
			writer.print(htmlText.toString());
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
	}

	/**
	 * Holds counting measures of the comparison.
	 */
	private LinkedHashMap<ECountingMeasure, Integer> m_CountingMeasures;
	/**
	 * Overall time an external operation took. Needed since it does not track
	 * this measure by itself.
	 */
	private long m_ExternalOverallTime;
	/**
	 * Internal buffer for logged lines, can be flushed by using
	 * {@link #flushLogToLogger()}.
	 */
	private final List<String> m_LoggedLines;
	/**
	 * The logger used by the Ultimate framework.
	 */
	private final Logger m_Logger;
	/**
	 * The inputed buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Operand;
	/**
	 * The resulting buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;
	/**
	 * Service provider of Ultimate framework.
	 */
	private final AutomataLibraryServices m_Services;
	/**
	 * Holds time measures of the comparison.
	 */
	private LinkedHashMap<ETimeMeasure, Float> m_TimeMeasures;

	/**
	 * Compares the different types of simulation methods for buechi reduction.
	 * Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to compare with
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 * @throws IllegalArgumentException
	 *             If the inputed automaton is no Buechi-automaton. It must have
	 *             an empty call and return alphabet.
	 */
	public CompareReduceBuchiSimulation(final AutomataLibraryServices services, final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		if (!operand.getCallAlphabet().isEmpty() || !operand.getReturnAlphabet().isEmpty()) {
			throw new IllegalArgumentException(
					"The inputed automaton is no Buechi-automaton. It must have an empty call and return alphabet.");
		}

		m_LoggedLines = new LinkedList<String>();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Result = operand;
		m_TimeMeasures = new LinkedHashMap<>();
		m_CountingMeasures = new LinkedHashMap<>();
		m_ExternalOverallTime = 0;

		m_Logger.info(startMessage());

		createAndResetPerformanceHead();
		appendPerformanceHeadToLog();

		long simulationTimeoutMillis = SIMULATION_TIMEOUT * ComparisonTables.SECONDS_TO_MILLIS;

		// Remove dead ends, a requirement of simulation
		NestedWordAutomatonReachableStates<LETTER, STATE> operandReachable = new RemoveUnreachable<LETTER, STATE>(
				m_Services, new RemoveNonLiveStates<LETTER, STATE>(m_Services, operand).getResult()).getResult();

		String automatonName = "";
//		BufferedReader br = null;
//		try {
//			br = new BufferedReader(new FileReader(new File(LOG_PATH, "currentAutomatonName.txt")));
//			while (br.ready()) {
//				automatonName = br.readLine();
//			}
//		} catch (IOException e) {
//			e.printStackTrace();
//		} finally {
//			if (br != null) {
//				try {
//					br.close();
//				} catch (IOException e) {
//					e.printStackTrace();
//				}
//			}
//		}

		// Direct simulation without SCC
		measureMethodPerformance(automatonName, ESimulationType.DIRECT, false, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Direct simulation with SCC
		measureMethodPerformance(automatonName, ESimulationType.DIRECT, true, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Delayed simulation without SCC
		measureMethodPerformance(automatonName, ESimulationType.DELAYED, false, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Delayed simulation with SCC
		measureMethodPerformance(automatonName, ESimulationType.DELAYED, true, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Fair simulation without SCC
		measureMethodPerformance(automatonName, ESimulationType.FAIR, false, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Fair simulation with SCC
		measureMethodPerformance(automatonName, ESimulationType.FAIR, true, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Fair direct simulation without SCC
		measureMethodPerformance(automatonName, ESimulationType.FAIRDIRECT, false, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);
		// Fair direct simulation with SCC
		measureMethodPerformance(automatonName, ESimulationType.FAIRDIRECT, true, m_Services, simulationTimeoutMillis,
				stateFactory, operandReachable);

		// Other minimization methods
		measureMethodPerformance(automatonName, ESimulationType.EXT_MINIMIZESEVPA, true, m_Services,
				simulationTimeoutMillis, stateFactory, operandReachable);
		measureMethodPerformance(automatonName, ESimulationType.EXT_SHRINKNWA, true, m_Services,
				simulationTimeoutMillis, stateFactory, operandReachable);

		// flushLogToLogger();
		flushLogToFile();

		m_Logger.info(exitMessage());
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#checkResult(
	 * de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory)
	 */
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#exitMessage()
	 */
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ".";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public Object getResult() throws AutomataLibraryException {
		return m_Result;
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#operationName()
	 */
	@Override
	public String operationName() {
		return "compareReduceBuchiSimulation";
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see
	 * de.uni_freiburg.informatik.ultimate.automata.IOperation#startMessage()
	 */
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Operand has " + m_Operand.sizeInformation();
	}

	/**
	 * Appends the current saved state of the performance as an entry to the
	 * log.
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
	private void appendCurrentPerformanceEntryToLog(final String name, final ESimulationType type,
			final boolean usedSCCs, final boolean timedOut, final boolean outOfMemory) {
		// Fix fields
		String message = name + LOG_SEPARATOR + type + LOG_SEPARATOR + usedSCCs + LOG_SEPARATOR + timedOut
				+ LOG_SEPARATOR + outOfMemory;
		// Variable fields
		for (Float measureValue : m_TimeMeasures.values()) {
			message += LOG_SEPARATOR + measureValue;
		}
		for (Integer measureValue : m_CountingMeasures.values()) {
			message += LOG_SEPARATOR + measureValue;
		}
		logLine(message);
	}

	/**
	 * Measures the effectiveness of a given method for buechi reduction and
	 * logs it.
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
	 * @throws AutomataLibraryException
	 *             If a automata library exception occurred.
	 */
	@SuppressWarnings("unchecked")
	private void appendMethodPerformanceToLog(final Object method, final String name, final ESimulationType type,
			final boolean usedSCCs, final boolean timedOut, final boolean outOfMemory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) throws AutomataLibraryException {
		createAndResetPerformanceHead();

		if (method instanceof ASimulation) {
			ASimulation<LETTER, STATE> simulation = (ASimulation<LETTER, STATE>) method;
			SimulationPerformance performance = simulation.getSimulationPerformance();

			if (timedOut) {
				performance.timeOut();
			}
			if (outOfMemory) {
				performance.outOfMemory();
			}
			performance.setName(name);
			saveStateOfPerformance(performance);
		} else if (method instanceof MinimizeSevpa) {
			MinimizeSevpa<LETTER, STATE> minimizeSevpa = (MinimizeSevpa<LETTER, STATE>) method;
			INestedWordAutomatonOldApi<LETTER, STATE> methodResult = minimizeSevpa.getResult();
			// Removed states
			if (methodResult != null) {
				int removedStates = m_Operand.size() - methodResult.size();
				m_CountingMeasures.put(ECountingMeasure.REMOVED_STATES, removedStates);
			}
			// Buechi states
			m_CountingMeasures.put(ECountingMeasure.BUCHI_STATES, operand.size());
			// Overall time
			m_TimeMeasures.put(ETimeMeasure.OVERALL_TIME, ComparisonTables.millisToSeconds(m_ExternalOverallTime));
		} else if (method instanceof ShrinkNwa) {
			ShrinkNwa<LETTER, STATE> shrinkNwa = (ShrinkNwa<LETTER, STATE>) method;
			INestedWordAutomatonSimple<LETTER, STATE> methodResult = shrinkNwa.getResult();
			// Removed states
			if (methodResult != null) {
				int removedStates = m_Operand.size() - methodResult.size();
				m_CountingMeasures.put(ECountingMeasure.REMOVED_STATES, removedStates);
			}
			// Buechi states
			m_CountingMeasures.put(ECountingMeasure.BUCHI_STATES, operand.size());
			// Overall time
			m_TimeMeasures.put(ETimeMeasure.OVERALL_TIME, ComparisonTables.millisToSeconds(m_ExternalOverallTime));
		}

		if (timedOut && method == null) {
			saveStateOfPerformance(createTimedOutPerformance(name, type, usedSCCs, operand));
		} else if (outOfMemory && method == null) {
			saveStateOfPerformance(createOutOfMemoryPerformance(name, type, usedSCCs, operand));
		}

		appendCurrentPerformanceEntryToLog(name, type, usedSCCs, timedOut, outOfMemory);
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
		for (ETimeMeasure measure : m_TimeMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}
		for (ECountingMeasure measure : m_CountingMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}

		message += LOG_ENTRY_HEAD_END;

		logLine(message);
	}

	/**
	 * Creates or resets the head of the performance format.
	 */
	private void createAndResetPerformanceHead() {
		for (ETimeMeasure measure : ETimeMeasure.values()) {
			m_TimeMeasures.put(measure, (float) SimulationPerformance.NO_TIME_RESULT);
		}
		for (ECountingMeasure measure : ECountingMeasure.values()) {
			m_CountingMeasures.put(measure, SimulationPerformance.NO_COUNTING_RESULT);
		}
	}

	/**
	 * Creates an out of memory performance object and adds some information of
	 * the used method.
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
	private SimulationPerformance createOutOfMemoryPerformance(final String name, final ESimulationType type,
			final boolean useSCCs, final INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		SimulationPerformance performance = SimulationPerformance.createOutOfMemoryPerformance(type, useSCCs);
		performance.setName(name);
		performance.setCountingMeasure(ECountingMeasure.BUCHI_STATES, operand.size());
		return performance;
	}

	/**
	 * Creates a timed out performance object and adds some information of the
	 * timed out method.
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
	private SimulationPerformance createTimedOutPerformance(final String name, final ESimulationType type,
			final boolean useSCCs, final INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		SimulationPerformance performance = SimulationPerformance.createTimedOutPerformance(type, useSCCs);
		performance.setName(name);
		performance.setCountingMeasure(ECountingMeasure.BUCHI_STATES, operand.size());
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
		File dataFile = new File(LOG_PATH, LOG_PATH_DATA);
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(dataFile, true)));
			for (String message : m_LoggedLines) {
				writer.println(message);
			}
		} catch (IOException e) {
			e.printStackTrace();
		} finally {
			if (writer != null) {
				writer.close();
			}
		}
		m_Logger.info("Logged data to file (" + dataFile.getAbsolutePath() + ").");
	}

	/**
	 * Flushes the internal buffered log messages to the used logger.
	 */
	@SuppressWarnings("unused")
	private void flushLogToLogger() {
		for (String message : m_LoggedLines) {
			m_Logger.info(message);
		}
	}

	/**
	 * Logs a given message as single line. Uses a internal buffer that needs to
	 * be flushed in order to actually print the logs. Flushing is done by using
	 * {@link #flushLogToLogger()}.
	 * 
	 * @param message
	 *            Message to log
	 */
	private void logLine(final String message) {
		m_LoggedLines.add(message);
	}

	/**
	 * Measures the performance of a simulation, represented by a given type, on
	 * a given automaton and appends its performance to the log.
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
	 *            A time duration, in milliseconds, after which the method
	 *            should automatically timeout and abort.
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 */
	private void measureMethodPerformance(final String name, final ESimulationType type, final boolean useSCCs,
			final AutomataLibraryServices services, final long timeout, final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) {
		IProgressAwareTimer progressTimer = services.getProgressMonitorService().getChildTimer(timeout);
		boolean timedOut = false;
		boolean outOfMemory = false;
		Object method = null;

		try {
			if (type.equals(ESimulationType.DIRECT)) {
				method = new DirectSimulation<>(services, progressTimer, m_Logger, operand, useSCCs, stateFactory);
			} else if (type.equals(ESimulationType.DELAYED)) {
				method = new DelayedSimulation<>(services, progressTimer, m_Logger, operand, useSCCs, stateFactory);
			} else if (type.equals(ESimulationType.FAIR)) {
				method = new FairSimulation<>(services, progressTimer, m_Logger, operand, useSCCs, stateFactory);
			} else if (type.equals(ESimulationType.FAIRDIRECT)) {
				method = new FairDirectSimulation<>(services, progressTimer, m_Logger, operand, useSCCs, stateFactory);
			} else if (type.equals(ESimulationType.EXT_MINIMIZESEVPA)) {
				long startTime = System.currentTimeMillis();
				method = new MinimizeSevpa<LETTER, STATE>(m_Services, operand);
				m_ExternalOverallTime = System.currentTimeMillis() - startTime;
			} else if (type.equals(ESimulationType.EXT_SHRINKNWA)) {
				long startTime = System.currentTimeMillis();
				method = new ShrinkNwa<>(m_Services, stateFactory, operand);
				m_ExternalOverallTime = System.currentTimeMillis() - startTime;
			}
		} catch (OperationCanceledException e) {
			m_Logger.info("Method timed out.");
			timedOut = true;
		} catch (AutomataLibraryException e) {
			e.printStackTrace();
		} catch (OutOfMemoryError e) {
			m_Logger.info("Method has thrown an out of memory error.");
			outOfMemory = true;
		}
		try {
			appendMethodPerformanceToLog(method, name, type, useSCCs, timedOut, outOfMemory, operand);
		} catch (AutomataLibraryException e) {
			e.printStackTrace();
		}
	}

	/**
	 * Saves the state of a given performance in internal fields.
	 * 
	 * @param performance
	 *            Performance to save
	 */
	private void saveStateOfPerformance(final SimulationPerformance performance) {
		for (ETimeMeasure measure : m_TimeMeasures.keySet()) {
			long durationInMillis = performance.getTimeMeasureResult(measure, EMultipleDataOption.ADDITIVE);
			if (durationInMillis == SimulationPerformance.NO_TIME_RESULT) {
				m_TimeMeasures.put(measure, (float) SimulationPerformance.NO_TIME_RESULT);
			} else {
				m_TimeMeasures.put(measure, ComparisonTables.millisToSeconds(durationInMillis));
			}
		}
		for (ECountingMeasure measure : m_CountingMeasures.keySet()) {
			int counter = performance.getCountingMeasureResult(measure);
			m_CountingMeasures.put(measure, counter);
		}
	}
}
