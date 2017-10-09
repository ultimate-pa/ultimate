/*
 * Copyright (C) 2014-2017 Daniel Tischner <zabuza.dev@gmail.com>
 * Copyright (C) 2009-2017 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.performance;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardOpenOption;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.simulation.performance.CompareReduceBuchiSimulation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IIntersectionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.ISinkStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.IRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.Minimize;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.minimization.hopcroft.MinimizeNftaHopcroft;

/**
 * Operation that compares the different types of methods for tree automata
 * reduction. The operation has no result, it automatically logs performance
 * measurements to a log file.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 * @param <LETTER>
 *            Letter class of tree automaton
 * @param <STATE>
 *            State class of tree automaton
 */
public final class CompareTaMinimization<LETTER extends IRankedLetter, STATE>
		extends GeneralOperation<LETTER, STATE, IStateFactory<STATE>> {
	/**
	 * Path where performance measurement relevant logs and data gets saved.
	 */
	public static final Path LOG_PATH = Paths.get(System.getProperty("user.home"), "Desktop", "performanceMeasurement");

	/**
	 * Separator that is used in the log.
	 */
	public static final String LOG_SEPARATOR = "\t";
	/**
	 * Name for the object of the log file.
	 */
	private static final String LOG_PATH_DATA = "testData.tsv";

	/**
	 * Reads the log file and creates readable performance tables as HTML files.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void main(final String[] args) throws IOException {
		System.out.println("Parsing log file...");
		final Path dataFile = LOG_PATH.resolve(LOG_PATH_DATA);
		final List<String> lines = Files.readAllLines(dataFile);

		System.out.println("Creating html files...");
		CompareReduceBuchiSimulation.tableToHtmlFile("instanceFullComparison", lines);

		System.out.println("Terminated.");
	}

	/**
	 * Logs the head message to the log file.
	 * 
	 * @param dataFile
	 *            The file to log to
	 */
	private static void logHead(final Path dataFile) {
		final ArrayList<String> columns = new ArrayList<>();
		columns.add("name");
		columns.add("size");
		columns.add("rules");
		columns.add("ordinary_type");
		columns.add("ordinary_time");
		columns.add("ordinary_timedOut");
		columns.add("ordinary_oom");
		columns.add("ordinary_size");
		columns.add("ordinary_rules");
		columns.add("hopcroft_type");
		columns.add("hopcroft_time");
		columns.add("hopcroft_timedOut");
		columns.add("hopcroft_oom");
		columns.add("hopcroft_size");
		columns.add("hopcroft_rules");

		final String line = String.join(LOG_SEPARATOR, columns);

		try {
			Files.write(dataFile, Collections.singletonList(line), StandardOpenOption.CREATE, StandardOpenOption.WRITE);
		} catch (final IOException e) {
			e.printStackTrace();
		}
	}

	/**
	 * The name of the automaton.
	 */
	private final String mAutomatonName;

	/**
	 * Internal buffer for logged lines, can be flushed by using
	 * {@link #flushLogToFile()}.
	 */
	private final List<String> mLoggedLines;

	/**
	 * The operand tree automaton to minimize.
	 */
	private final ITreeAutomatonBU<LETTER, STATE> mOperand;

	/**
	 * Factory used to merge states and create sink states.
	 */
	private final SinkMergeIntersectStateFactory<STATE> mSinkAndMergeFactory;

	/**
	 * Compares the different types of methods for tree automata reduction. The
	 * operation has no result, it automatically logs performance measurements to a
	 * log file.
	 * 
	 * @param <SF>
	 *            A state factory that is able to merge and intersect states and
	 *            also to create sink states
	 *
	 * @param services
	 *            Service provider of Ultimate framework
	 * @param sinkMergeIntersectFactory
	 *            The factory to use for merging and intersecting states and also
	 *            for creating sink states
	 * @param operand
	 *            The tree automaton to compare with
	 */
	public <SF extends IMergeStateFactory<STATE> & ISinkStateFactory<STATE> & IIntersectionStateFactory<STATE>> CompareTaMinimization(
			final AutomataLibraryServices services, final SF sinkMergeIntersectFactory,
			final ITreeAutomatonBU<LETTER, STATE> operand) {
		super(services);
		this.mSinkAndMergeFactory = new SinkMergeIntersectStateFactory<>(sinkMergeIntersectFactory,
				sinkMergeIntersectFactory, sinkMergeIntersectFactory);
		this.mOperand = operand;
		this.mLoggedLines = new LinkedList<>();

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		String automatonName = "";
//		try {
//			automatonName = Files.lines(LOG_PATH.resolve("currentAutomatonName.txt")).findFirst().get();
//		} catch (final IOException e) {
//			e.printStackTrace();
//		}
		this.mAutomatonName = automatonName;

		measurePerformances();
		flushLogToFile();

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(exitMessage());
		}
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
	 * Flushes the internal buffered log messages to a file on the desktop.
	 */
	private void flushLogToFile() {
		// If logging directory does not exist, try to create it
		if (!Files.exists(LOG_PATH)) {
			try {
				Files.createDirectories(LOG_PATH);
			} catch (final IOException e) {
				e.printStackTrace();
			}
		}

		// Write to file
		final Path dataFile = LOG_PATH.resolve(LOG_PATH_DATA);

		if (!Files.exists(dataFile)) {
			logHead(dataFile);
		}

		try {
			Files.write(dataFile, this.mLoggedLines, StandardOpenOption.APPEND, StandardOpenOption.CREATE,
					StandardOpenOption.WRITE);
		} catch (final IOException e) {
			e.printStackTrace();
		}
		this.mLoggedLines.clear();

		this.mLogger.info("Logged data to file (" + dataFile.toAbsolutePath() + ").");
	}

	/**
	 * Logs a given message as single line. Uses a internal buffer that needs to be
	 * flushed in order to actually print the logs. Flushing is done by using
	 * {@link #flushLogToFile()}.
	 *
	 * @param message
	 *            Message to log
	 */
	private void logLine(final String message) {
		this.mLoggedLines.add(message);
	}

	/**
	 * Logs the given results, also appends miscellaneous information and
	 * information about the operand before minimization.
	 * 
	 * @param allResults
	 *            All results to log
	 */
	private void logResults(final String[]... allResults) {
		// AutomatonName
		final String[] misc = new String[] { this.mAutomatonName };
		// Size, amountOfRules
		final String[] beforeResults = new String[] { Integer.toString(this.mOperand.size()),
				Integer.toString(this.mOperand.getAmountOfRules()) };

		// Collect all results
		final ArrayList<String> completeResults = new ArrayList<>();
		completeResults.addAll(Arrays.asList(misc));
		completeResults.addAll(Arrays.asList(beforeResults));
		Arrays.asList(allResults).forEach(results -> completeResults.addAll(Arrays.asList(results)));

		// Join and log
		final String line = String.join(LOG_SEPARATOR, completeResults);
		logLine(line);
	}

	/**
	 * Measures the performance of a minimization methods, represented by a given
	 * type, on a given automaton and returns the results.
	 *
	 * @param type
	 *            Type of the minimization method to measure performance for
	 * @return The measured results
	 */
	@SuppressWarnings("unchecked")
	protected String[] measureMethodPerformance(final String type) {
		boolean timedOut = false;
		boolean outOfMemory = false;
		long overallTime = -1;
		Object method = null;

		try {
			if (type.equalsIgnoreCase("ordinary")) {
				final long startTime = System.currentTimeMillis();
				method = new Minimize<>(this.mServices, this.mSinkAndMergeFactory, this.mOperand);
				overallTime = System.currentTimeMillis() - startTime;
			} else if (type.equalsIgnoreCase("hopcroft")) {
				final long startTime = System.currentTimeMillis();
				method = new MinimizeNftaHopcroft<>(this.mServices, this.mSinkAndMergeFactory, this.mOperand);
				overallTime = System.currentTimeMillis() - startTime;
			} else {
				throw new IllegalArgumentException("Unsupported type of minimization");
			}
		} catch (final AutomataOperationCanceledException e) {
			this.mLogger.info("Method timed out.");
			timedOut = true;
		} catch (final OutOfMemoryError e) {
			this.mLogger.info("Method has thrown an out of memory error.");
			outOfMemory = true;
		}

		ITreeAutomatonBU<LETTER, STATE> resultingTa = null;
		if (method instanceof IOperation) {
			final Object resultRaw = ((IOperation<LETTER, STATE, IStateFactory<STATE>>) method).getResult();
			if (resultRaw instanceof ITreeAutomatonBU) {
				resultingTa = (ITreeAutomatonBU<LETTER, STATE>) resultRaw;
			}
		}
		if (resultingTa == null) {
			throw new AssertionError("Result is null but must not be. Cast-logic may be incorrect.");
		}

		// Type, time, timedOut, outOfMemory, resultSize, resultAmountOfRules
		final String[] results = new String[] { type, Long.toString(overallTime), Boolean.toString(timedOut),
				Boolean.toString(outOfMemory), Integer.toString(resultingTa.size()),
				Integer.toString(resultingTa.getAmountOfRules()) };
		return results;
	}

	/**
	 * Starts measuring performances for all minimization methods to compare.
	 *
	 */
	protected void measurePerformances() {
		// Ordinary minimization
		final String[] ordinaryResults = measureMethodPerformance("ordinary");

		// Hopcroft minimization
		final String[] hopcroftResults = measureMethodPerformance("hopcroft");

		logResults(ordinaryResults, hopcroftResults);
	}

}
