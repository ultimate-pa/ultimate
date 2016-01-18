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
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintWriter;
import java.math.BigDecimal;
import java.math.RoundingMode;
import java.util.ArrayList;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

import org.apache.log4j.Logger;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.OperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.ASimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.delayed.DelayedSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.direct.DirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairDirectSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.buchiReduction.fair.FairSimulation;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.MinimizeSevpa;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.ShrinkNwa;
import de.uni_freiburg.informatik.ultimate.core.services.model.IProgressAwareTimer;
import de.uni_freiburg.informatik.ultimate.core.services.model.IUltimateServiceProvider;

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
	 * Decimal places to round duration of a method to.
	 */
	private final static int DECIMAL_PLACES = 2;
	/**
	 * Amount of fix fields in the log format. Currently this is type and
	 * usedSCCs.
	 */
	private final static int FIX_FIELD_AMOUNT = 2;
	/**
	 * File object of the html file.
	 */
	private static final File HTMLFILE = new File(new File(System.getProperty("user.home"), "Desktop"),
			"simulationPerformanceTestResults.html");
	/**
	 * Marks the end of the head from an entry.
	 */
	private final static String LOG_ENTRY_HEAD_END = "-->";
	/**
	 * Marks the start of the head from an entry.
	 */
	private final static String LOG_ENTRY_HEAD_START = "<!--";
	/**
	 * Separator that is used in the log.
	 */
	private final static String LOG_SEPARATOR = "\t";
	/**
	 * File object of the log file.
	 */
	private static final File LOGFILE = new File(new File(System.getProperty("user.home"), "Desktop"),
			"simulationPerformanceTestData.tsv");

	/**
	 * Factor that, if multiplied with, converts seconds to milliseconds.
	 */
	private final static int SECONDS_TO_MILLIS = 1000;

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
		List<String> table = createInstanceFullComparisonTable(performanceEntries);

		System.out.println("Creating html file...");
		tableToHtmlFile(table);

		System.out.println("Terminated.");
	}

	/**
	 * Creates a table that holds the full comparison data for each automata
	 * instance respectively.
	 * 
	 * @param performanceEntries
	 *            Data structure holding the performance entries
	 * @return A table in a tsv-like format, specified by
	 *         {@link #LOG_SEPARATOR}.
	 */
	private static List<String> createInstanceFullComparisonTable(
			final LinkedList<LinkedList<SimulationPerformance>> performanceEntries) {
		List<String> table = new LinkedList<>();
		if (performanceEntries.isEmpty()) {
			return table;
		}

		// Header of table
		String header = "TYPE" + LOG_SEPARATOR + "USED_SCCS";
		SimulationPerformance headerCandidate = performanceEntries.get(0).get(0);
		Set<TimeMeasure> timeMeasures = headerCandidate.getTimeMeasures().keySet();
		for (TimeMeasure measure : timeMeasures) {
			header += LOG_SEPARATOR + measure;
		}
		Set<CountingMeasure> countingMeasures = headerCandidate.getCountingMeasures().keySet();
		for (CountingMeasure measure : countingMeasures) {
			header += LOG_SEPARATOR + measure;
		}
		table.add(header);

		for (LinkedList<SimulationPerformance> performanceComparison : performanceEntries) {
			for (SimulationPerformance performanceOfSimulation : performanceComparison) {
				SimulationType type = performanceOfSimulation.getSimType();

				// Fix fields
				String row = type + LOG_SEPARATOR + performanceOfSimulation.isUsingSCCs();

				// Variable fields
				for (TimeMeasure measure : timeMeasures) {
					float value = millisToSeconds(
							performanceOfSimulation.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE));
					String valueAsString = value + "";
					if (value < 0) {
						valueAsString = "&ndash;";
					}
					row += LOG_SEPARATOR + valueAsString;
				}
				for (CountingMeasure measure : countingMeasures) {
					int value = performanceOfSimulation.getCountingMeasureResult(measure);
					String valueAsString = value + "";
					if (value < 0) {
						valueAsString = "&ndash;";
					}
					row += LOG_SEPARATOR + valueAsString;
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
	 * rounds it to two places after the decimal.
	 * 
	 * @param millis
	 *            Value, representing milliseconds, that should be converted
	 * @return The given value in seconds, rounded to two places after the
	 *         decimal.
	 */
	private static float millisToSeconds(final long millis) {
		BigDecimal secondsAsBigDecimal = new BigDecimal((millis + 0.0) / SECONDS_TO_MILLIS);
		secondsAsBigDecimal = secondsAsBigDecimal.setScale(DECIMAL_PLACES, RoundingMode.HALF_UP);
		float seconds = secondsAsBigDecimal.floatValue();
		return seconds;
	}

	/**
	 * Parses the file {@link #LOGFILE} and sets a data structure up which holds
	 * all data from the log file.
	 * 
	 * @return A data structure holding all data from the log file.
	 */
	@SuppressWarnings("unchecked")
	private static LinkedList<LinkedList<SimulationPerformance>> parseLogFile() {
		BufferedReader br = null;
		try {
			LinkedList<LinkedList<SimulationPerformance>> performanceEntries = new LinkedList<>();
			LinkedList<SimulationPerformance> currentPerformanceEntry = null;
			ArrayList<TimeMeasure> currentTimeMeasures = new ArrayList<>();
			ArrayList<CountingMeasure> currentCountingMeasures = new ArrayList<>();

			// Setup isValidEnum - Map
			HashMap<String, TimeMeasure> nameToTimeMeasure = new HashMap<>();
			for (TimeMeasure measure : TimeMeasure.values()) {
				nameToTimeMeasure.put(measure.name(), measure);
			}
			HashMap<String, CountingMeasure> nameToCountingMeasure = new HashMap<>();
			for (CountingMeasure measure : CountingMeasure.values()) {
				nameToCountingMeasure.put(measure.name(), measure);
			}

			br = new BufferedReader(new FileReader(LOGFILE));
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
					SimulationType type = SimulationType.valueOf(lineElements[0]);
					boolean usedSCCs = Boolean.parseBoolean(lineElements[1]);
					SimulationPerformance performance = new SimulationPerformance(type, usedSCCs);

					// Parse the rest of the data set
					for (int i = FIX_FIELD_AMOUNT; i < lineElements.length; i++) {
						int indexTimeMeasure = i - FIX_FIELD_AMOUNT;
						int indexCountingMeasure = i - FIX_FIELD_AMOUNT - currentTimeMeasures.size();
						if (indexTimeMeasure >= 0 && indexTimeMeasure < currentTimeMeasures.size()) {
							TimeMeasure measure = currentTimeMeasures.get(indexTimeMeasure);
							performance.addTimeMeasureValue(measure,
									secondsToMillis(Float.parseFloat(lineElements[i])));
						} else if (indexCountingMeasure >= 0 && indexCountingMeasure < currentCountingMeasures.size()) {
							CountingMeasure measure = currentCountingMeasures.get(indexCountingMeasure);
							performance.setCountingMeasure(measure, Integer.parseInt(lineElements[i]));
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
	 * Converts a given float value, representing seconds, to milliseconds.
	 * 
	 * @param seconds
	 *            Value, representing seconds, that should be converted
	 * @return The given value in milliseconds.
	 */
	private static long secondsToMillis(final float seconds) {
		return Math.round(seconds * SECONDS_TO_MILLIS);
	}

	/**
	 * Parses a table, in a format like .csv or .tsv where
	 * {@link #LOG_SEPARATOR} is the separator. The parsed table then is writen
	 * to a html-file on the desktop.
	 * 
	 * @param table
	 *            Table to convert
	 */
	private static void tableToHtmlFile(List<String> table) {
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
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(HTMLFILE)));
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
	private LinkedHashMap<CountingMeasure, Integer> m_CountingMeasures;
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
	 * The resulting possible reduced buechi automaton.
	 */
	private final INestedWordAutomatonOldApi<LETTER, STATE> m_Result;

	/**
	 * Service provider of Ultimate framework.
	 */
	private final IUltimateServiceProvider m_Services;

	/**
	 * Holds time measures of the comparison.
	 */
	private LinkedHashMap<TimeMeasure, Float> m_TimeMeasures;

	/**
	 * Compares the different types of simulation methods for buechi reduction.
	 * Resulting automaton is the input automaton.
	 * 
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param stateFactory
	 *            The state factory used for creating states
	 * @param operand
	 *            The buechi automaton to reduce
	 * @throws OperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public CompareReduceBuchiSimulation(final IUltimateServiceProvider services, final StateFactory<STATE> stateFactory,
			final INestedWordAutomatonOldApi<LETTER, STATE> operand) throws OperationCanceledException {
		m_LoggedLines = new LinkedList<String>();
		m_Services = services;
		m_Logger = m_Services.getLoggingService().getLogger(LibraryIdentifiers.s_LibraryID);
		m_Operand = operand;
		m_Result = operand;
		m_TimeMeasures = new LinkedHashMap<>();
		m_CountingMeasures = new LinkedHashMap<>();

		m_Logger.info(startMessage());
		try {
			createAndResetPerformanceHead();
			appendPerformanceHeadToLog();
			
			// TODO the new way to obtain timeout
			long tenSeconds = 2 * 1000;
			IProgressAwareTimer pat = services.getProgressMonitorService().getChildTimer(tenSeconds);

			// Direct simulation without SCC
			appendMethodPerformanceToLog(new DirectSimulation<>(services, operand, false, stateFactory));
			// Direct simulation with SCC
			appendMethodPerformanceToLog(new DirectSimulation<>(services, operand, true, stateFactory));

			// Delayed simulation without SCC
			appendMethodPerformanceToLog(new DelayedSimulation<>(services, operand, false, stateFactory));
			// Delayed simulation with SCC
			appendMethodPerformanceToLog(new DelayedSimulation<>(services, operand, true, stateFactory));

			// Fair simulation without SCC
			appendMethodPerformanceToLog(new FairSimulation<>(services, operand, false, stateFactory));
			// Fair simulation with SCC
			appendMethodPerformanceToLog(new FairSimulation<>(services, operand, true, stateFactory));

			// Fair direct simulation without SCC
			appendMethodPerformanceToLog(new FairDirectSimulation<>(services, operand, false, stateFactory));
			// Fair direct simulation with SCC
			appendMethodPerformanceToLog(new FairDirectSimulation<>(services, operand, true, stateFactory));

			// Other minimization methods
			// TODO Fix problem with not possible cast to IDoubleDecker
			// startTimeMeasure();
			// measureMethodEffectiveness("MinimizeSevpa", new
			// MinimizeSevpa<>(services, operand));
			// startTimeMeasure();
			// measureMethodEffectiveness("ShrinkNwa", new ShrinkNwa<>(services,
			// stateFactory, operand));
		} catch (AutomataLibraryException e) {
			e.printStackTrace();
		} finally {
			// flushLogToLogger();
			flushLogToFile();
		}
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
	 * @param type
	 *            Type of the used method
	 * @param usedSCCs
	 *            If SCCs where used by the method
	 */
	private void appendCurrentPerformanceEntry(SimulationType type, boolean usedSCCs) {
		// Fix fields
		String message = type + LOG_SEPARATOR + usedSCCs + LOG_SEPARATOR;
		// Variable fields
		for (Float measureValue : m_TimeMeasures.values()) {
			message += measureValue + LOG_SEPARATOR;
		}
		for (Integer measureValue : m_CountingMeasures.values()) {
			message += measureValue + LOG_SEPARATOR;
		}
		logLine(message);
	}

	/**
	 * Measures the effectiveness of a given method for buechi reduction and
	 * logs it.<br/>
	 * The format of the log is:
	 * <tt>NAME\tSCCS\tDURATION\tREMOVED_STATES\tREMOVED_TRANSITIONS\
	 * tSIMULATION_STEPS\tFAILED_MERGE_ATTEMPTS\tFAILED_TRANSREMOVE_ATTEMPTS<tt>
	 * where duration is in seconds.
	 * 
	 * @param method
	 *            Used method
	 * @throws AutomataLibraryException
	 *             If a automata library exception occurred.
	 */
	@SuppressWarnings("unchecked")
	private void appendMethodPerformanceToLog(final Object method) throws AutomataLibraryException {
		createAndResetPerformanceHead();

		SimulationType type = null;
		boolean usedSCCs = false;

		INestedWordAutomatonOldApi<LETTER, STATE> methodResult = null;
		if (method instanceof ASimulation) {
			ASimulation<LETTER, STATE> simulation = (ASimulation<LETTER, STATE>) method;
			SimulationPerformance performance = simulation.getSimulationPerformance();

			for (TimeMeasure measure : m_TimeMeasures.keySet()) {
				long durationInMillis = performance.getTimeMeasureResult(measure, MultipleDataOption.ADDITIVE);
				m_TimeMeasures.put(measure, millisToSeconds(durationInMillis));
			}
			for (CountingMeasure measure : m_CountingMeasures.keySet()) {
				int counter = performance.getCountingMeasureResult(measure);
				m_CountingMeasures.put(measure, counter);
			}
			// Method type
			type = performance.getSimType();
			// Used SCCs
			usedSCCs = performance.isUsingSCCs();

		} else if (method instanceof MinimizeSevpa) {
			MinimizeSevpa<LETTER, STATE> minimizeSevpa = (MinimizeSevpa<LETTER, STATE>) method;
			methodResult = minimizeSevpa.getResult();
			// Removed states
			if (m_CountingMeasures.containsKey(CountingMeasure.REMOVED_STATES)) {
				if (methodResult != null) {
					int removedStates = m_Operand.size() - methodResult.size();
					m_CountingMeasures.put(CountingMeasure.REMOVED_STATES, removedStates);
				}
			}
		} else if (method instanceof ShrinkNwa) {
			ShrinkNwa<LETTER, STATE> shrinkNwa = (ShrinkNwa<LETTER, STATE>) method;
			methodResult = (INestedWordAutomatonOldApi<LETTER, STATE>) shrinkNwa.getResult();
			// Removed states
			if (m_CountingMeasures.containsKey(CountingMeasure.REMOVED_STATES)) {
				if (methodResult != null) {
					int removedStates = m_Operand.size() - methodResult.size();
					m_CountingMeasures.put(CountingMeasure.REMOVED_STATES, removedStates);
				}
			}
		}

		appendCurrentPerformanceEntry(type, usedSCCs);
	}

	/**
	 * Appends the head of the performance format to the log.
	 */
	private void appendPerformanceHeadToLog() {
		String message = LOG_ENTRY_HEAD_START + LOG_SEPARATOR;

		// Fix fields
		message += "TYPE" + LOG_SEPARATOR + "USED_SCCS" + LOG_SEPARATOR;
		// Variable fields
		for (TimeMeasure measure : m_TimeMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}
		for (CountingMeasure measure : m_CountingMeasures.keySet()) {
			message += measure + LOG_SEPARATOR;
		}

		message += LOG_ENTRY_HEAD_END;

		logLine(message);
	}

	/**
	 * Creates or resets the head of the performance format.
	 */
	private void createAndResetPerformanceHead() {
		m_TimeMeasures.put(TimeMeasure.OVERALL_TIME, (float) SimulationPerformance.NO_TIME_RESULT);
		m_CountingMeasures.put(CountingMeasure.SIMULATION_STEPS, SimulationPerformance.NO_COUNTING_RESULT);
		m_CountingMeasures.put(CountingMeasure.REMOVED_STATES, SimulationPerformance.NO_COUNTING_RESULT);
		m_CountingMeasures.put(CountingMeasure.REMOVED_TRANSITIONS, SimulationPerformance.NO_COUNTING_RESULT);
		m_CountingMeasures.put(CountingMeasure.FAILED_MERGE_ATTEMPTS, SimulationPerformance.NO_COUNTING_RESULT);
		m_CountingMeasures.put(CountingMeasure.FAILED_TRANSREMOVE_ATTEMPTS, SimulationPerformance.NO_COUNTING_RESULT);
	}

	/**
	 * Flushes the internal buffered log messages to a file on the desktop.
	 */
	private void flushLogToFile() {
		PrintWriter writer = null;
		try {
			writer = new PrintWriter(new BufferedWriter(new FileWriter(LOGFILE, true)));
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
		m_Logger.info("Logged data to file (" + LOGFILE.getAbsolutePath() + ").");
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
}
