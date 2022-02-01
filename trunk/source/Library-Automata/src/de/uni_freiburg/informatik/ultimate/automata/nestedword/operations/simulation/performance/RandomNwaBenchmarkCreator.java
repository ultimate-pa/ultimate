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
import java.util.Collections;
import java.util.Date;
import java.util.LinkedList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.Analyze.SymbolType;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNwa;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNwaTv;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;

/**
 * Creates a set of random Nwa automata and saves them as ats-Files.
 *
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class RandomNwaBenchmarkCreator {

	/**
	 * Default path where the Nwa automata benchmark set gets saved if no other path is specified.
	 */
	public static final File DEFAULT_PATH =
			new File(new File(System.getProperty("user.home"), "Desktop"), "randomNwaBenchmark");
	/**
	 * Default amount of created Nwa automata after which a logging message gets printed.
	 */
	public static final int LOG_EVERY = 100;
	/**
	 * The lower bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_LOWER_BOUND = 0;
	/**
	 * Converts a value in percentage, if multiplied with, into a value between 0.0 and 1.0.
	 */
	private static final int PERC_TO_DOUBLE = 100;
	/**
	 * The upper bound for a value that can be interpreted as percentage.
	 */
	private static final int PERC_UPPER_BOUND = 100;

	/**
	 * The percentage of how many states should be accepting, between 0 and 100 (both inclusive).
	 */
	private final float mAcceptance;
	/**
	 * The size of the alphabet generated Nwa automata should have.
	 */
	private final int mAlphabetSize;
	/**
	 * The percentage of how many call transitions each state should be have, between 0 and 100 (both inclusive).
	 */
	private final float mCallTotality;
	/**
	 * The percentage of how many hierarchical predecessor for return transitions each state should have, greater equals
	 * 0.
	 */
	private final float mHierarchicalPredecessorDensity;
	/**
	 * The percentage of how many internal transitions each state should be have, between 0 and 100 (both inclusive).
	 */
	private final float mInternalTotality;
	/**
	 * The text that gets saved in every following created ats-File right before the automaton itself. Can be used to
	 * write operations, that use the automaton, directly in the same file.
	 */
	private String mPreamble;
	/**
	 * The percentage of how many return transitions each state should be have, between 0 and 100 (both inclusive).
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
	 * If <tt>true</tt> {@link GetRandomNwaTv}, else {@link GetRandomNwa} gets used for creation.
	 */
	private final boolean mUseRandomTvModel;

	/**
	 * Creates a new creator object that is able to generate random automata with the given properties. A benchmark set
	 * can then be created using {@link #createAndSaveABenchmark(int, File, int)}. This constructor internally uses
	 * {@link GetRandomNwa}.
	 *
	 * @param size
	 *            The amount of states generated Nwa automata should have
	 * @param alphabetSize
	 *            The size of the alphabet generated Nwa automata should have
	 * @param acceptance
	 *            The percentage of how many states should be accepting, between 0 and 100 (both inclusive)
	 * @param internalTotality
	 *            The percentage of how many internal transitions each state should be have, between 0 and 100 (both
	 *            inclusive)
	 * @param callTotality
	 *            The percentage of how many call transitions each state should be have, between 0 and 100 (both
	 *            inclusive)
	 * @param returnTotality
	 *            The percentage of how many return transitions each state should be have, between 0 and 100 (both
	 *            inclusive)
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
		mHierarchicalPredecessorDensity = -1f;
		mUseRandomTvModel = false;

		mServices = new AutomataLibraryServices(new ToolchainStorage());
		mPreamble = "";
	}

	/**
	 * Creates a new creator object that is able to generate random automata with the given properties. A benchmark set
	 * can then be created using {@link #createAndSaveABenchmark(int, File, int)}. This constructor internally uses
	 * {@link GetRandomNwaTv}.
	 *
	 * @param size
	 *            The amount of states generated Nwa automata should have
	 * @param alphabetSize
	 *            The size of the alphabet generated Nwa automata should have
	 * @param acceptance
	 *            The percentage of how many states should be accepting, between 0 and 100 (both inclusive)
	 * @param internalDensity
	 *            The percentage of how many internal transitions each state should have, greater equals 0
	 * @param callDensity
	 *            The percentage of how many call transitions each state should have, greater equals 0
	 * @param returnDensity
	 *            The percentage of how many return transitions each state should have, greater equals 0
	 * @param hierarchicalPredecessorDensity
	 *            The percentage of how many hierarchical predecessor for return transitions each state should have,
	 *            greater equals 0
	 * @throws IllegalArgumentException
	 *             If a percentage value is not in the given range.
	 */
	public RandomNwaBenchmarkCreator(final int size, final int alphabetSize, final float acceptance,
			final float internalDensity, final float callDensity, final float returnDensity,
			final float hierarchicalPredecessorDensity) throws IllegalArgumentException {
		mSize = size;
		mAlphabetSize = alphabetSize;
		mAcceptance = ensureIsPercentage(acceptance);
		mInternalTotality = internalDensity;
		mCallTotality = callDensity;
		mReturnTotality = returnDensity;
		mHierarchicalPredecessorDensity = hierarchicalPredecessorDensity;
		mUseRandomTvModel = true;

		mServices = new AutomataLibraryServices(new ToolchainStorage());
		mPreamble = "";
	}

	/**
	 * Creates and saves random generated Nwa automata to the default path, specified by {@link #DEFAULT_PATH}, in the
	 * ats-Format. Prints a debug message to {@link System#out} after every {@link #LOG_EVERY} created automata.
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
	 * Creates and saves random generated Nwa automata to the given path in the ats-Format. Prints a debug message to
	 * {@link System#out} after every {@link #LOG_EVERY} created automata.
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
	 * Creates and saves random generated Nwa automata to the given path in the ats-Format.
	 *
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param pathToSaveBenchmark
	 *            The path where the automata should get saved
	 * @param logEvery
	 *            Amount of generated automata after which a logging message gets printed to {@link System#out}
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

			// Use the appropriate method depending on the input
			if (mUseRandomTvModel) {
				nwa = new GetRandomNwaTv(mServices, mSize, mAlphabetSize, mAlphabetSize, mAlphabetSize,
						(int) mInternalTotality, (int) mCallTotality, (int) mReturnTotality,
						(int) mHierarchicalPredecessorDensity, (int) mAcceptance).getResult();
			} else {
				nwa = new GetRandomNwa(mServices, mAlphabetSize, mSize, internalTotalityDouble, callTotalityDouble,
						returnTotalityDouble, acceptanceDouble, 0L).getResult();
			}

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
	 * Creates and saves random generated Nwa automata to the default path, specified by {@link #DEFAULT_PATH}, in the
	 * ats-Format. Prints a debug message to {@link System#out} after every {@link #LOG_EVERY} created automata.
	 *
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param folderName
	 *            Name of the folder to save the files in, the folder itself is located at the default path
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public void createAndSaveABenchmark(final int amount, final String folderName) throws IOException {
		createAndSaveABenchmark(amount, new File(DEFAULT_PATH, folderName), LOG_EVERY);
	}

	/**
	 * Sets a text that gets saved in every following created ats-File right before the automaton itself. Can be used to
	 * write operations, that use the automaton, directly in the same file.
	 *
	 * @param preamble
	 *            Text to set right before the generated automata
	 */
	public void setPreamble(final String preamble) {
		mPreamble = preamble;
	}

	/**
	 * Ensures the given value is a percentage. For this, it must be between 0 and 100 (both inclusive).
	 *
	 * @param percentage
	 *            Value to ensure
	 * @return The given value if it is valid
	 * @throws IllegalArgumentException
	 *             If the given value is no percentage, i.e. not between 0 and 100 (both inclusive)
	 */
	private float ensureIsPercentage(final float percentage) throws IllegalArgumentException {
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
	private double percentageToDouble(final float percentage) {
		return percentage / PERC_TO_DOUBLE;
	}

	/**
	 * Shows the usage of the {@link RandomNwaBenchmarkCreator} class.
	 *
	 * @param args
	 *            Not supported
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	public static void main(final String[] args) throws IOException {
		// Settings for both methods
		final int n = 100;
		final int k = 2;
		final int amount = 20;
		final int operationSwitch = 0;
		final boolean useRandomTvModel = true;

		// Settings for explicit set
		final float acceptanceInPerc = 50;
		final float totalityInternalInPerc = 50f;
		final float totalityCallInPerc = 50f;
		final float totalityReturnInPerc = 1f;
		final float totalityHierPredInPerc = 50f;

		// Settings for space coverage sets
		final float acceptanceInPercMin = 50f;
		final float acceptanceInPercMax = 50f;
		final float totalityInternalInPercMin = 1f;
		final float totalityInternalInPercMax = 300f;
		final float totalityCallInPercMin = 0f;
		final float totalityCallInPercMax = 0f;
		final float totalityReturnInPercMin = 0f;
		final float totalityReturnInPercMax = 0f;
		final float totalityHierPredInPercMin = 0f;
		final float totalityHierPredInPercMax = 0f;
		final int stepSize = 2;
		final boolean uniformStep = true;

		// Which method to use
		final boolean createExplicit = false;

		if (createExplicit) {
			createExplicitSet(n, k, acceptanceInPerc, totalityInternalInPerc, totalityCallInPerc, totalityReturnInPerc,
					totalityHierPredInPerc, amount, operationSwitch, useRandomTvModel);
		} else {
			coverSpaceBenchmark(n, k, amount, operationSwitch, useRandomTvModel, acceptanceInPercMin,
					acceptanceInPercMax, totalityInternalInPercMin, totalityInternalInPercMax, totalityCallInPercMin,
					totalityCallInPercMax, totalityReturnInPercMin, totalityReturnInPercMax, totalityHierPredInPercMin,
					totalityHierPredInPercMax, stepSize, uniformStep);
		}
	}

	/**
	 * Creates benchmark sets that cover the whole given spice by using the {@link RandomNwaBenchmarkCreator} class.
	 * 
	 * @param n
	 *            The amount of states generated Nwa automata should have
	 * @param k
	 *            The size of the alphabet generated Nwa automata should have
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param operationSwitch
	 *            Which operation to use
	 * @param useRandomTvModel
	 *            If the random TV-Model should be used for generation
	 * @param acceptanceInPercMin
	 *            The minimum percentage of how many states should be accepting, between 0 and 100 (both inclusive)
	 * @param acceptanceInPercMax
	 *            The maximum percentage of how many states should be accepting, between 0 and 100 (both inclusive)
	 * @param totalityInternalInPercMin
	 *            The minimum percentage of how many internal transitions each state should have, greater equals 0
	 * @param totalityInternalInPercMax
	 *            The maximum percentage of how many internal transitions each state should have, greater equals 0
	 * @param totalityCallInPercMin
	 *            The minimum percentage of how many call transitions each state should have, greater equals 0
	 * @param totalityCallInPercMax
	 *            The maximum percentage of how many call transitions each state should have, greater equals 0
	 * @param totalityReturnInPercMin
	 *            The minimum percentage of how many return transitions each state should have, greater equals 0
	 * @param totalityReturnInPercMax
	 *            The maximum percentage of how many return transitions each state should have, greater equals 0
	 * @param totalityHierPredInPercMin
	 *            The minimum percentage of how many hierarchical predecessor for return transitions each state should
	 *            have, greater equals 0
	 * @param totalityHierPredInPercMax
	 *            The maximum percentage of how many hierarchical predecessor for return transitions each state should
	 *            have, greater equals 0
	 * @param stepSize
	 *            How big the steps between each iteration should be
	 * @param uniformStep
	 *            If <tt>true</tt> each parameter will equally be increased at the same time. If <tt>false</tt> they
	 *            will be changed independently.
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	private static void coverSpaceBenchmark(final int n, final int k, final int amount, final int operationSwitch,
			final boolean useRandomTvModel, final float acceptanceInPercMin, final float acceptanceInPercMax,
			final float totalityInternalInPercMin, final float totalityInternalInPercMax,
			final float totalityCallInPercMin, final float totalityCallInPercMax, final float totalityReturnInPercMin,
			final float totalityReturnInPercMax, final float totalityHierPredInPercMin,
			final float totalityHierPredInPercMax, final float stepSize, final boolean uniformStep) throws IOException {
		System.out.println("Starting creation of space coverage sets...");

		int acceptanceSteps = (int) Math.ceil((acceptanceInPercMax - acceptanceInPercMin) / stepSize);
		if (acceptanceSteps == 0) {
			acceptanceSteps = 1;
		}
		int internalSteps = (int) Math.ceil((totalityInternalInPercMax - totalityInternalInPercMin) / stepSize);
		if (internalSteps == 0) {
			internalSteps = 1;
		}
		int callSteps = (int) Math.ceil((totalityCallInPercMax - totalityCallInPercMin) / stepSize);
		if (callSteps == 0) {
			callSteps = 1;
		}
		int returnSteps = (int) Math.ceil((totalityReturnInPercMax - totalityReturnInPercMin) / stepSize);
		if (returnSteps == 0) {
			returnSteps = 1;
		}
		int hierPredSteps = (int) Math.ceil((totalityHierPredInPercMax - totalityHierPredInPercMin) / stepSize);
		if (hierPredSteps == 0) {
			hierPredSteps = 1;
		}

		int stepsToGo;
		if (uniformStep) {
			final List<Integer> steps = new LinkedList<>();
			steps.add(acceptanceSteps);
			steps.add(internalSteps);
			steps.add(callSteps);
			steps.add(returnSteps);
			steps.add(hierPredSteps);
			stepsToGo = Collections.max(steps);
		} else {
			stepsToGo = acceptanceSteps * internalSteps * callSteps * returnSteps * hierPredSteps;
		}
		System.out.println("Sets to create: " + stepsToGo);
		System.out.println("---------------");

		if (uniformStep) {
			final List<Float> minPercentages = new LinkedList<>();
			minPercentages.add(acceptanceInPercMin);
			minPercentages.add(totalityInternalInPercMin);
			minPercentages.add(totalityCallInPercMin);
			minPercentages.add(totalityReturnInPercMin);
			minPercentages.add(totalityHierPredInPercMin);
			final float smallestPercentage = Collections.min(minPercentages);
			final List<Float> maxPercentages = new LinkedList<>();
			maxPercentages.add(acceptanceInPercMax);
			maxPercentages.add(totalityInternalInPercMax);
			maxPercentages.add(totalityCallInPercMax);
			maxPercentages.add(totalityReturnInPercMax);
			maxPercentages.add(totalityHierPredInPercMax);
			final float greatestPercentage = Collections.max(maxPercentages);

			for (float percentage = smallestPercentage; percentage <= greatestPercentage; percentage += stepSize) {
				float acceptanceInPerc;
				if (percentage < acceptanceInPercMin) {
					acceptanceInPerc = acceptanceInPercMin;
				} else if (percentage > acceptanceInPercMax) {
					acceptanceInPerc = acceptanceInPercMax;
				} else {
					acceptanceInPerc = percentage;
				}

				float totalityInternalInPerc;
				if (percentage < totalityInternalInPercMin) {
					totalityInternalInPerc = totalityInternalInPercMin;
				} else if (percentage > totalityInternalInPercMax) {
					totalityInternalInPerc = totalityInternalInPercMax;
				} else {
					totalityInternalInPerc = percentage;
				}

				float totalityCallInPerc;
				if (percentage < totalityCallInPercMin) {
					totalityCallInPerc = totalityCallInPercMin;
				} else if (percentage > totalityCallInPercMax) {
					totalityCallInPerc = totalityCallInPercMax;
				} else {
					totalityCallInPerc = percentage;
				}

				float totalityReturnInPerc;
				if (percentage < totalityReturnInPercMin) {
					totalityReturnInPerc = totalityReturnInPercMin;
				} else if (percentage > totalityReturnInPercMax) {
					totalityReturnInPerc = totalityReturnInPercMax;
				} else {
					totalityReturnInPerc = percentage;
				}

				float totalityHierPredInPerc;
				if (percentage < totalityHierPredInPercMin) {
					totalityHierPredInPerc = totalityHierPredInPercMin;
				} else if (percentage > totalityHierPredInPercMax) {
					totalityHierPredInPerc = totalityHierPredInPercMax;
				} else {
					totalityHierPredInPerc = percentage;
				}

				createExplicitSet(n, k, acceptanceInPerc, totalityInternalInPerc, totalityCallInPerc,
						totalityReturnInPerc, totalityHierPredInPerc, amount, operationSwitch, useRandomTvModel);
				stepsToGo--;
				System.out.println("Steps to go: " + stepsToGo);
			}

		} else {
			for (float acceptanceInPerc =
					acceptanceInPercMin; acceptanceInPerc <= acceptanceInPercMax; acceptanceInPerc += stepSize) {
				for (float totalityInternalInPerc =
						totalityInternalInPercMin; totalityInternalInPerc <= totalityInternalInPercMax; totalityInternalInPerc +=
								stepSize) {
					for (float totalityCallInPerc =
							totalityCallInPercMin; totalityCallInPerc <= totalityCallInPercMax; totalityCallInPerc +=
									stepSize) {
						for (float totalityReturnInPerc =
								totalityReturnInPercMin; totalityReturnInPerc <= totalityReturnInPercMax; totalityReturnInPerc +=
										stepSize) {
							for (float totalityHierPredInPerc =
									totalityHierPredInPercMin; totalityHierPredInPerc <= totalityHierPredInPercMax; totalityHierPredInPerc +=
											stepSize) {
								createExplicitSet(n, k, acceptanceInPerc, totalityInternalInPerc, totalityCallInPerc,
										totalityReturnInPerc, totalityHierPredInPerc, amount, operationSwitch,
										useRandomTvModel);
								stepsToGo--;
								System.out.println("Steps to go: " + stepsToGo);
							}
						}
					}
				}
			}
		}
	}

	/**
	 * Creates a benchmark set with given explicit settings by using the {@link RandomNwaBenchmarkCreator} class.
	 * 
	 * @param n
	 *            The amount of states generated Nwa automata should have
	 * @param k
	 *            The size of the alphabet generated Nwa automata should have
	 * @param acceptanceInPerc
	 *            The percentage of how many states should be accepting, between 0 and 100 (both inclusive)
	 * @param totalityInternalInPerc
	 *            The percentage of how many internal transitions each state should have, greater equals 0
	 * @param totalityCallInPerc
	 *            The percentage of how many call transitions each state should have, greater equals 0
	 * @param totalityReturnInPerc
	 *            The percentage of how many return transitions each state should have, greater equals 0
	 * @param totalityHierPredInPerc
	 *            The percentage of how many hierarchical predecessor for return transitions each state should have,
	 *            greater equals 0
	 * @param amount
	 *            Amount of random Nwa automata to generate
	 * @param operationSwitch
	 *            Which operation to use
	 * @param useRandomTvModel
	 *            If the random TV-Model should be used for generation
	 * @throws IOException
	 *             If an I/O-Exception occurred
	 */
	private static void createExplicitSet(final int n, final int k, final float acceptanceInPerc,
			final float totalityInternalInPerc, final float totalityCallInPerc, final float totalityReturnInPerc,
			final float totalityHierPredInPerc, final int amount, final int operationSwitch,
			final boolean useRandomTvModel) throws IOException {
		final String operation;
		switch (operationSwitch) {
			case 0:
				operation = "compareReduceNwaSimulation(removeDeadEnds(nwa));";
				break;
			case 1:
				operation = "reduceNwaDirectSimulation(removeDeadEnds(nwa), false);";
				break;
			case 2:
				operation = "minimizeNwaPmaxSat(removeDeadEnds(nwa));";
				break;
			default:
				operation = "";
				break;
		}

		final String timeStamp = new SimpleDateFormat("yyyy/MM/dd HH:mm:ss").format(new Date());
		final String preamble = "// Random nwa automaton dumped by RandomNwaBenchmarkCreator at " + timeStamp + "\n"
				+ "// Author: Daniel Tischner {@literal <zabuza.dev@gmail.com>}\n\n" + operation + "\n\n";

		// Create the object and pass settings
		final RandomNwaBenchmarkCreator creator;
		if (useRandomTvModel) {
			creator = new RandomNwaBenchmarkCreator(n, k, acceptanceInPerc, totalityInternalInPerc, totalityCallInPerc,
					totalityReturnInPerc, totalityHierPredInPerc);
		} else {
			creator = new RandomNwaBenchmarkCreator(n, k, acceptanceInPerc, totalityInternalInPerc, totalityCallInPerc,
					totalityReturnInPerc);
		}
		creator.setPreamble(preamble);

		System.out.println("Starting automata generation.");
		String label;
		if (useRandomTvModel) {
			label = "#" + amount + "_n" + n + "_k" + k + "_f" + acceptanceInPerc + "%_ti" + totalityInternalInPerc
					+ "%_tc" + totalityCallInPerc + "%_tr" + totalityReturnInPerc + "%_th" + totalityHierPredInPerc
					+ "%";
		} else {
			label = "#" + amount + "_n" + n + "_k" + k + "_f" + acceptanceInPerc + "%_ti" + totalityInternalInPerc
					+ "%_tc" + totalityCallInPerc + "%_tr" + totalityReturnInPerc + "%";
		}

		creator.createAndSaveABenchmark(amount, label);
		System.out.println("Finished automata generation.");
		System.out.println("Overview label:");
		System.out.println(label);
	}
}
