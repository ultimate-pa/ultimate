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
import java.text.SimpleDateFormat;
import java.util.Arrays;
import java.util.Collections;
import java.util.Date;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.tree.ITreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.GetRandomDftaBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.operations.GetRandomNftaBU;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;

/**
 * Creates a set of random tree automata and saves them as ats-Files.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class RandomTaBenchmarkCreator {

	/**
	 * Default path where the tree automata benchmark set gets saved if no other
	 * path is specified.
	 */
	public static final Path DEFAULT_PATH = Paths.get(System.getProperty("user.home"), "Desktop", "randomTaBenchmark");
	/**
	 * Default amount of created tree automata after which a logging message gets
	 * printed.
	 */
	public static final int LOG_EVERY = 10;
	/**
	 * The lower bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_LOWER_BOUND = 0;
	/**
	 * Converts a value in percentage, if multiplied with, into a value between 0.0
	 * and 1.0.
	 */
	private static final int PERC_TO_DOUBLE = 100;
	/**
	 * The upper bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_UPPER_BOUND = 100;

	/**
	 * Shows the usage of the {@link RandomTaBenchmarkCreator} class.
	 *
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public static void main(final String[] args) throws IOException, AutomataOperationCanceledException {
		// Settings
		final int n = 20;
		final float acceptanceInPerc = 20;
		final int[] rankToK = new int[] { 2, 1, 3, 1 };
		final int[] rankToRulesPerLetter = new int[] { 3, 7, 2, 3 };
		final int amount = 100;
		final int operationSwitch = 0;
		final boolean createDeterministic = true;

		createExplicitSet(n, rankToK, acceptanceInPerc, rankToRulesPerLetter, amount, operationSwitch,
				createDeterministic);
	}

	/**
	 * Creates a benchmark set with given explicit settings by using the
	 * {@link RandomTaBenchmarkCreator} class.
	 * 
	 * @param n
	 *            The amount of states the generated tree automata should have
	 * @param rankToK
	 *            The size of the alphabet the generated tree automata should have,
	 *            per rank
	 * @param acceptanceInPerc
	 *            The percentage of how many states should be accepting, between 0
	 *            and 100 (both inclusive)
	 * @param rankToRulesPerLetter
	 *            The percentage of how many rules each letter should have, per rank
	 * @param amount
	 *            Amount of random tree automata to generate
	 * @param operationSwitch
	 *            Which operation to use
	 * @param createDeterministic
	 *            Whether only deterministic automata should be created
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private static void createExplicitSet(final int n, final int[] rankToK, final float acceptanceInPerc,
			final int[] rankToRulesPerLetter, final int amount, final int operationSwitch,
			final boolean createDeterministic) throws IOException, AutomataOperationCanceledException {
		final String operation;
		switch (operationSwitch) {
		case 0:
			operation = "compareTaMinimization(ta);";
			break;
		case 1:
			operation = "minimizeNftaHopcroft(ta);";
			break;
		case 2:
			operation = "minimize(ta);";
			break;
		default:
			operation = "";
			break;
		}

		final String timeStamp = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new Date());
		final String preamble = "// Random tree automaton dumped by RandomTaBenchmarkCreator at " + timeStamp + "\n"
				+ "// Author: Daniel Tischner {@literal <zabuza.dev@gmail.com>}\n\n" + operation
				+ "\n\nTreeAutomaton ta = ";
		final String postamble = ";";

		// Create the object and pass settings
		final RandomTaBenchmarkCreator creator;
		creator = new RandomTaBenchmarkCreator(n, rankToK, acceptanceInPerc, rankToRulesPerLetter, createDeterministic);
		creator.setPreamble(preamble);
		creator.setPostamble(postamble);

		System.out.println("Starting automata generation.");
		String label;
		label = "#" + amount + "_n" + n + "_k" + Arrays.toString(rankToK) + "_f" + acceptanceInPerc + "%_r"
				+ Arrays.toString(rankToRulesPerLetter) + "_det" + createDeterministic;

		creator.createAndSaveABenchmark(amount, label);
		System.out.println("Finished automata generation.");
		System.out.println("Overview label:");
		System.out.println(label);
	}

	/**
	 * Ensures the given value is a percentage. For this, it must be between 0 and
	 * 100 (both inclusive).
	 *
	 * @param percentage
	 *            Value to ensure
	 * @return The given value if it is valid
	 * @throws IllegalArgumentException
	 *             If the given value is no percentage, i.e. not between 0 and 100
	 *             (both inclusive)
	 */
	private static float ensureIsPercentage(final float percentage) throws IllegalArgumentException {
		if (percentage < PERC_LOWER_BOUND || percentage > PERC_UPPER_BOUND) {
			throw new IllegalArgumentException("The given value is no percentage: " + percentage);
		}
		return percentage;
	}

	/**
	 * Converts a given value, in percentage, to a double value between 0.0 and 1.0.
	 *
	 * @param percentage
	 *            Value between 0 and 100 (both inclusive).
	 * @return The corresponding value between 0.0 and 1.0
	 */
	private static double percentageToDouble(final float percentage) {
		return percentage / PERC_TO_DOUBLE;
	}

	/**
	 * The percentage of how many states should be accepting, between 0 and 100
	 * (both inclusive).
	 */
	private final float mAcceptance;

	/**
	 * Whether only deterministic automata should be created.
	 */
	private final boolean mCreateDeterministic;

	/**
	 * The text that gets saved in every following created ats-File right after the
	 * automaton itself. Can be used to write operations, that use the automaton,
	 * directly in the same file.
	 */
	private String mPostamble;

	/**
	 * The text that gets saved in every following created ats-File right before the
	 * automaton itself. Can be used to write operations, that use the automaton,
	 * directly in the same file.
	 */
	private String mPreamble;

	/**
	 * The size of the alphabet the generated tree automata should have, per rank.
	 */
	private final int[] mRankToAlphabetSize;

	/**
	 * The amount of how many rules each letter should have, per rank.
	 */
	private final int[] mRankToRulesPerLetter;

	/**
	 * The services object used for automata creation.
	 */
	private final AutomataLibraryServices mServices;

	/**
	 * The amount of states generated tree automata should have.
	 */
	private final int mSize;

	/**
	 * Creates a new creator object that is able to generate random automata with
	 * the given properties. A benchmark set can then be created using
	 * {@link #createAndSaveABenchmark(int, Path, int)}. This constructor internally
	 * uses {@link GetRandomNftaBU}.
	 *
	 * @param size
	 *            The amount of states generated tree automata should have
	 * @param rankToAlphabetSize
	 *            The size of the alphabet generated tree automata should have, per
	 *            rank
	 * @param acceptance
	 *            The percentage of how many states should be accepting, between 0
	 *            and 100 (both inclusive)
	 * @param rankToRulesPerLetter
	 *            The amount of how many rules each letter should have, per rank
	 * @param createDeterministic
	 *            Whether only deterministic automata should be created
	 * @throws IllegalArgumentException
	 *             If a percentage value is not between 0 and 100 (inclusive)
	 */
	public RandomTaBenchmarkCreator(final int size, final int[] rankToAlphabetSize, final float acceptance,
			final int[] rankToRulesPerLetter, final boolean createDeterministic) throws IllegalArgumentException {
		this.mSize = size;
		this.mRankToAlphabetSize = rankToAlphabetSize;
		this.mAcceptance = ensureIsPercentage(acceptance);
		this.mRankToRulesPerLetter = rankToRulesPerLetter;
		this.mCreateDeterministic = createDeterministic;

		this.mServices = new AutomataLibraryServices(new ToolchainStorage());
		this.mPreamble = "";
	}

	/**
	 * Creates and saves random generated tree automata to the default path,
	 * specified by {@link #DEFAULT_PATH}, in the ats-Format. Prints a debug message
	 * to {@link System#out} after every {@link #LOG_EVERY} created automata.
	 *
	 * @param amount
	 *            Amount of random tree automata to generate
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void createAndSaveABenchmark(final int amount) throws IOException, AutomataOperationCanceledException {
		createAndSaveABenchmark(amount, DEFAULT_PATH, LOG_EVERY);
	}

	/**
	 * Creates and saves random generated tree automata to the given path in the
	 * ats-Format. Prints a debug message to {@link System#out} after every
	 * {@link #LOG_EVERY} created automata.
	 *
	 * @param amount
	 *            Amount of random tree automata to generate
	 * @param pathToSaveBenchmark
	 *            The path where the automata should get saved to
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void createAndSaveABenchmark(final int amount, final Path pathToSaveBenchmark)
			throws IOException, AutomataOperationCanceledException {
		createAndSaveABenchmark(amount, pathToSaveBenchmark, LOG_EVERY);
	}

	/**
	 * Creates and saves random generated tree automata to the given path in the
	 * ats-Format.
	 *
	 * @param amount
	 *            Amount of random tree automata to generate
	 * @param pathToSaveBenchmark
	 *            The path where the automata should get saved to
	 * @param logEvery
	 *            Amount of generated automata after which a logging message gets
	 *            printed to {@link System#out}
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void createAndSaveABenchmark(final int amount, final Path pathToSaveBenchmark, final int logEvery)
			throws IOException, AutomataOperationCanceledException {
		ITreeAutomatonBU<StringRankedLetter, String> ta = null;

		final double acceptanceDouble = percentageToDouble(this.mAcceptance);

		final String timeStamp = new SimpleDateFormat("yyyyMMddHHmmss").format(new Date());
		final String fileName = "randomTreeAutomata_" + timeStamp;
		final String fileFormat = ".ats";

		if (!Files.exists(pathToSaveBenchmark)) {
			Files.createDirectories(pathToSaveBenchmark);
		} else if (!Files.isDirectory(pathToSaveBenchmark)) {
			throw new IllegalArgumentException("The provided path exists but is no directory: " + pathToSaveBenchmark);
		}

		for (int i = 1; i <= amount; i++) {
			if (i % logEvery == 0) {
				System.out.println("Created automata: " + i);
			}

			// Generate the automaton
			final long seed = System.currentTimeMillis();
			if (this.mCreateDeterministic) {
				ta = new GetRandomDftaBU(this.mServices, this.mSize, this.mRankToAlphabetSize,
						this.mRankToRulesPerLetter, acceptanceDouble, seed).getResult();
			} else {
				ta = new GetRandomNftaBU(this.mServices, this.mSize, this.mRankToAlphabetSize,
						this.mRankToRulesPerLetter, acceptanceDouble, seed).getResult();
			}

			if (i == 1) {
				// Print some debug information
				System.out.println("#Rules: " + ta.getAmountOfRules());
			}

			final String fileNamePost = "_" + i;
			final Path automatonFile = pathToSaveBenchmark.resolve(fileName + fileNamePost + fileFormat);

			Files.write(automatonFile, Collections.singletonList(this.mPreamble + ta + this.mPostamble));
		}
	}

	/**
	 * Creates and saves random generated tree automata to the default path,
	 * specified by {@link #DEFAULT_PATH}, in the ats-Format. Prints a debug message
	 * to {@link System#out} after every {@link #LOG_EVERY} created automata.
	 *
	 * @param amount
	 *            Amount of random tree automata to generate
	 * @param folderName
	 *            Name of the folder to save the files in, the folder itself is
	 *            located at the default path
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public void createAndSaveABenchmark(final int amount, final String folderName)
			throws IOException, AutomataOperationCanceledException {
		createAndSaveABenchmark(amount, DEFAULT_PATH.resolve(folderName), LOG_EVERY);
	}

	/**
	 * Sets a text that gets saved in every following created ats-File right after
	 * the automaton itself. Can be used to write operations, that use the
	 * automaton, directly in the same file.
	 *
	 * @param postamble
	 *            Text to set right after the generated automata
	 */
	public void setPostamble(final String postamble) {
		this.mPostamble = postamble;
	}

	/**
	 * Sets a text that gets saved in every following created ats-File right before
	 * the automaton itself. Can be used to write operations, that use the
	 * automaton, directly in the same file.
	 *
	 * @param preamble
	 *            Text to set right before the generated automata
	 */
	public void setPreamble(final String preamble) {
		this.mPreamble = preamble;
	}
}
