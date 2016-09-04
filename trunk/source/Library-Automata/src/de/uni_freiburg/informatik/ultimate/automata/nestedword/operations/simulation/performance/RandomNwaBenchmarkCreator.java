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

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.text.SimpleDateFormat;
import java.util.Date;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;

/**
 * Creates a set of random Nwa automata and saves them as ats-Files.
 * 
 * @author Daniel Tischner
 *
 */
public final class RandomNwaBenchmarkCreator {

	/**
	 * Default path where the Nwa automata benchmark set gets saved if no other
	 * path is specified.
	 */
	public static final File DEFAULT_PATH = new File(new File(System.getProperty("user.home"), "Desktop"),
			"randomNwaBenchmark");
	/**
	 * Default amount of created Nwa automata after which a logging message gets
	 * printed.
	 */
	public static final int LOG_EVERY = 50;
	/**
	 * The lower bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_LOWER_BOUND = 0;
	/**
	 * Converts a value in percentage, if multiplied with, into a value between
	 * 0.0 and 1.0.
	 */
	private static final int PERC_TO_DOUBLE = 100;
	/**
	 * The upper bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_UPPER_BOUND = 100;

	/**
	 * Shows the usage of the {@link RandomNwaBenchmarkCreator} class.
	 * 
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void main(final String[] args) throws IOException {
		final int n = 50;
		final int k = 2;
		final float acceptanceInPerc = 50;
		final float totalityInternalInPerc = 1;
		final float totalityCallInPerc = 0.15f;
		final float totalityReturnInPerc = 0.003f;
		final int amount = 1000;
		final boolean operationSwitchUseCompareReduce = false;

		final String operation;
		if (operationSwitchUseCompareReduce) {
			operation = "compareReduceNwaSimulation(removeDeadEnds(nwa));";
		} else {
			operation = "reduceNwaDirectSimulation(removeDeadEnds(nwa), false);";
		}

		final String timeStamp = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new Date());
		final String preamble = "// Random nwa automaton dumped by RandomNwaBenchmarkCreator at " + timeStamp + "\n"
				+ "// Author: Daniel Tischner\n\n" + operation + "\n\n";

		// Create the object and pass settings
		final RandomNwaBenchmarkCreator creator = new RandomNwaBenchmarkCreator(n, k, acceptanceInPerc,
				totalityInternalInPerc, totalityCallInPerc, totalityReturnInPerc);
		creator.setPreamble(preamble);

		System.out.println("Starting automata generation.");
		creator.createAndSaveABenchmark(amount);
		System.out.println("Finished automata generation.");
	}

	/**
	 * The percentage of how many states should be accepting, between 0 and 100
	 * (both inclusive).
	 */
	private final float mAcceptance;
	/**
	 * The size of the alphabet generated Nwa automata should have.
	 */
	private final int mAlphabetSize;
	/**
	 * The percentage of how many call transitions each state should be have,
	 * between 0 and 100 (both inclusive).
	 */
	private final float mCallTotality;
	/**
	 * The percentage of how many internal transitions each state should be
	 * have, between 0 and 100 (both inclusive).
	 */
	private final float mInternalTotality;
	private String mPreamble;
	/**
	 * The percentage of how many return transitions each state should be have,
	 * between 0 and 100 (both inclusive).
	 */
	private final float mReturnTotality;

	/**
	 * The services object used for automata creation.
	 */
	private final AutomataLibraryServices mServices;

	/**
	 * The amount of states generated Nwa automata should have.
	 */
	private final int mSize;

	/**
	 * Creates a new creator object that is able to generate random automata
	 * with the given properties. A benchmark set can then be created using
	 * {@link #createAndSaveABenchmark(int, File, int)}.
	 * 
	 * @param size
	 *            The amount of states generated Nwa automata should have
	 * @param alphabetSize
	 *            The size of the alphabet generated Nwa automata should have
	 * @param acceptance
	 *            The percentage of how many states should be accepting, between
	 *            0 and 100 (both inclusive)
	 * @param internalTotality
	 *            The percentage of how many internal transitions each state
	 *            should be have, between 0 and 100 (both inclusive)
	 * @param callTotality
	 *            The percentage of how many call transitions each state should
	 *            be have, between 0 and 100 (both inclusive)
	 * @param returnTotality
	 *            The percentage of how many return transitions each state
	 *            should be have, between 0 and 100 (both inclusive)
	 * @throws IllegalArgumentException
	 *             If a percentage value is not between 0 and 100 (inclusive)
	 */
	public RandomNwaBenchmarkCreator(final int size, final int alphabetSize, final float acceptance,
			final float internalTotality, final float callTotality, final float returnTotality)
					throws IllegalArgumentException {
		mSize = size;
		mAlphabetSize = alphabetSize;
		mAcceptance = ensureIsPercentage(acceptance);
		mInternalTotality = ensureIsPercentage(internalTotality);
		mCallTotality = ensureIsPercentage(callTotality);
		mReturnTotality = ensureIsPercentage(returnTotality);

		mServices = new AutomataLibraryServices(new ToolchainStorage());
		mPreamble = "";
	}

	/**
	 * Creates and saves random generated Nwa automata to the default path,
	 * specified by {@link #DEFAULT_PATH}, in the ats-Format. Prints a debug
	 * message to {@link System#out} after every {@link #LOG_EVERY} created
	 * automata.
	 * 
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public void createAndSaveABenchmark(final int amount) throws IOException {
		createAndSaveABenchmark(amount, DEFAULT_PATH, LOG_EVERY);
	}

	/**
	 * Creates and saves random generated Nwa automata to the given path in the
	 * ats-Format. Prints a debug message to {@link System#out} after every
	 * {@link #LOG_EVERY} created automata.
	 * 
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param pathToSaveBenchmark
	 *            The path where the automata should get saved
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public void createAndSaveABenchmark(final int amount, final File pathToSaveBenchmark) throws IOException {
		createAndSaveABenchmark(amount, pathToSaveBenchmark, LOG_EVERY);
	}

	/**
	 * Creates and saves random generated Nwa automata to the given path in the
	 * ats-Format.
	 * 
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param pathToSaveBenchmark
	 *            The path where the automata should get saved
	 * @param logEvery
	 *            Amount of generated automata after which a logging message
	 *            gets printed to {@link System#out}
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public void createAndSaveABenchmark(final int amount, final File pathToSaveBenchmark, final int logEvery)
			throws IOException {
		INestedWordAutomaton<String, String> nwa = null;

		final double internalTotalityDouble = percentageToDouble(mInternalTotality);
		final double callTotalityDouble = percentageToDouble(mCallTotality);
		final double returnTotalityDouble = percentageToDouble(mReturnTotality);
		final double acceptanceDouble = percentageToDouble(mAcceptance);

		final String timeStamp = new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());
		final String fileName = "randomNwaAutomata_" + timeStamp;
		final String fileFormat = ".ats";

		if (!pathToSaveBenchmark.exists()) {
			pathToSaveBenchmark.mkdirs();
		} else if (!pathToSaveBenchmark.isDirectory()) {
			throw new IllegalArgumentException("The provided path exists but is no directory: " + pathToSaveBenchmark);
		}

		for (int i = 1; i <= amount; i++) {
			if (i % logEvery == 0) {
				System.out.println("Created automata: " + i);
			}

			nwa = new GetRandomNwa(mServices, mAlphabetSize, mSize, internalTotalityDouble, callTotalityDouble,
					returnTotalityDouble, acceptanceDouble).getResult();
			
			if (i == 1) {
				// Print some debug information
				final Analyze<String, String> analyzer = new Analyze<>(mServices, nwa, true);
				System.out.println("#Internal: " + analyzer.getNumberOfTransitions(SymbolType.INTERNAL));
				System.out.println("#Call: " + analyzer.getNumberOfTransitions(SymbolType.CALL));
				System.out.println("#Return: " + analyzer.getNumberOfTransitions(SymbolType.RETURN));
			}

			final String fileNamePost = "_" + i;
			final File automatonFile = new File(pathToSaveBenchmark, fileName + fileNamePost + fileFormat);

			final FileWriter fw = new FileWriter(automatonFile);
			fw.write(mPreamble + nwa);
			fw.close();
		}
	}

	/**
	 * Sets a text that gets saved in every following created ats-File right
	 * before the automaton itself. Can be used to write operations, that use
	 * the automaton, directly in the same file.
	 * 
	 * @param preamble
	 *            Text to set right before the generated automata
	 */
	public void setPreamble(final String preamble) {
		mPreamble = preamble;
	}

	/**
	 * Ensures the given value is a percentage. For this, it must be between 0
	 * and 100 (both inclusive).
	 * 
	 * @param percentage
	 *            Value to ensure
	 * @return The given value if it is valid
	 * @throws IllegalArgumentException
	 *             If the given value is no percentage, i.e. not between 0 and
	 *             100 (both inclusive)
	 */
	private float ensureIsPercentage(final float percentage) throws IllegalArgumentException {
		if (percentage < PERC_LOWER_BOUND || percentage > PERC_UPPER_BOUND) {
			throw new IllegalArgumentException("The given value is no percentage: " + percentage);
		}
		return percentage;
	}

	/**
	 * Converts a given value, in percentage, to a double value between 0.0 and
	 * 1.0.
	 * 
	 * @param percentage
	 *            Value between 0 and 100 (both inclusive).
	 * @return The corresponding value between 0.0 and 1.0
	 */
	private double percentageToDouble(final float percentage) {
		return percentage / PERC_TO_DOUBLE;
	}
}
