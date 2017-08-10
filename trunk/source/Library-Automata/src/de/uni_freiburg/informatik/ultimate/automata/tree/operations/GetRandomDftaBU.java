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
package de.uni_freiburg.informatik.ultimate.automata.tree.operations;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;
import de.uni_freiburg.informatik.ultimate.core.coreplugin.services.ToolchainStorage;
import de.uni_freiburg.informatik.ultimate.core.model.services.IProgressAwareTimer;

/**
 * Creates a random deterministic finite bottom-up tree automaton (DFTA-BU).
 * Note that the generation is not uniform.
 * <p>
 * The algorithm is similar to the one described in<br>
 * <ul>
 * <li><i>2013 Hanneforth, Thomas et al. - Random Generation of Nondeterministic
 * Finite-State Tree Automata.</i></li>
 * </ul>
 * Roughly said the algorithm randomly selects source and destination nodes in
 * each round, connecting them with a random transition.
 * 
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public final class GetRandomDftaBU extends GeneralOperation<StringRankedLetter, String, IStateFactory<String>> {
	/**
	 * The default seed to use for generation. It is not indented to change thus the
	 * result of using the default seed will always remain the same even in
	 * different JVM cycles.
	 */
	private static final long DEFAULT_SEED = 0;
	/**
	 * Prefix that is used for letters.
	 */
	private static final String LETTER_PREFIX = "a";
	/**
	 * Constant used for loop detection. If this factor is reached then the loop is
	 * aborted and it is assumed that a loop was entered.
	 */
	private static final int LOOP_DETECTION_GIVE_UP_FACTOR = 5;
	/**
	 * Prefix that is used for states.
	 */
	private static final String STATE_PREFIX = "q";
	/**
	 * If the rank of a letter increases beyond this threshold for the amount of
	 * states then a different method will be used for transition source
	 * generation.<br>
	 * <br>
	 * If its beyond the threshold then all states will be shuffled and then
	 * <tt>k</tt> source states are pulled, this ensures that no state will be
	 * selected multiple times but has the drawback of shuffling all states.<br>
	 * <br>
	 * If it is below the threshold then a random state will be selected and this
	 * process continues until an available state was found if it was already
	 * occupied. The drawback is that the closer the rank gets to the number of
	 * states the more repetitions are needed to find available states.
	 */
	private static double USE_SHUFFLE_ALL_METHOD_THRESHOLD = 0.75;

	/**
	 * Computes the absolute amount after applying a density to a total number. If
	 * for example the total number would be <tt>50</tt> and the density
	 * <tt>0.1</tt> then the result would be <tt>5</tt>. The method ensures that
	 * <tt>0</tt> is only returned if the density was precisely <tt>0.0</tt>.
	 * 
	 * @param density
	 *            The density to apply
	 * @param numberOfTotal
	 *            The total number to apply
	 * @return The absolute amount after applying the given density to the total
	 *         number
	 */
	private static int densityToAbsolute(final double density, final int numberOfTotal) {
		final int resultRaw = (int) (density * numberOfTotal);
		if (resultRaw > 0) {
			return resultRaw;
		}

		// Make sure the result is only zero if the density is precisely zero, else we
		// will return the closest possible integer which is one.
		if (density == 0.0) {
			return 0;
		}

		return 1;
	}

	/**
	 * The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then all states
	 * are accepting, if <tt>0</tt> then no state is accepting.
	 */
	private final double mAcceptanceDensity;
	/**
	 * The number of states {@code (>= 0)}.
	 */
	private final int mNumberOfStates;
	/**
	 * Timer used for responding to timeouts and operation cancellation.
	 */
	private final IProgressAwareTimer mProgressAwareTimer;
	/**
	 * Each index stands for the rank of a letter. The value stored at an index
	 * represents the amount of letters with that rank should be generated. Each
	 * value is {@code >= 0}.
	 */
	private final int[] mRankToNumberOfLetters;

	/**
	 * Each index stands for the rank of a letter. The value stored at an index
	 * represents the density {@code (0 <= x <= 1)} of transitions of that rank. The
	 * density of nullary letters specify the amount of initial states.
	 */
	private final double[] mRankToTransitionDensity;

	/**
	 * The resulting tree automaton after generation.
	 */
	private final TreeAutomatonBU<StringRankedLetter, String> mResult;

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}. This method uses a default seed that is not
	 * indented to change thus the result of this method, for same arguments, will
	 * always remain the same even in different JVM cycles. Use
	 * {@link #GetRandomNfta(AutomataLibraryServices, int, double, double, double, long, int...)}
	 * if a seed should be specified.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToTransitionDensity
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the density {@code (0 <= x <= 1)} of transitions
	 *            of that rank. Note that the density of nullary letters specify the
	 *            amount of initial states thus if initial states are desired
	 *            <code>rankToTransitionDensity[0]</code> should be set to a value
	 *            greater than <tt>zero</tt>.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final double[] rankToTransitionDensity, final double acceptanceDensity)
			throws AutomataOperationCanceledException {
		this(services, numberOfStates, rankToNumberOfLetters, rankToTransitionDensity, acceptanceDensity, DEFAULT_SEED);
	}

	/**
	 * Constructor of a deterministic finite tree automaton for the
	 * {@code TestFileInterpreter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            The number of states {@code (>= 0)}
	 * @param rankToNumberOfLetters
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of letters with that rank should be
	 *            generated. Each value must be {@code >= 0}. Note that in order to
	 *            have initial states there must exist at least one nullary letter,
	 *            so <code>rankToNumberOfLetters[0]</code> should be set to a value
	 *            greater than <tt>zero</tt> if initial states are desired.
	 * @param rankToTransitionDensity
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the density {@code (0 <= x <= 1)} of transitions
	 *            of that rank. Note that the density of nullary letters specify the
	 *            amount of initial states thus if initial states are desired
	 *            <code>rankToTransitionDensity[0]</code> should be set to a value
	 *            greater than <tt>zero</tt>.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @param seed
	 *            The seed to use for random automaton generation.
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	public GetRandomDftaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final double[] rankToTransitionDensity, final double acceptanceDensity,
			final long seed) throws AutomataOperationCanceledException {
		super(services);
		this.mProgressAwareTimer = this.mServices.getProgressAwareTimer();

		this.mNumberOfStates = numberOfStates;
		this.mRankToNumberOfLetters = rankToNumberOfLetters;
		this.mRankToTransitionDensity = rankToTransitionDensity;
		this.mAcceptanceDensity = acceptanceDensity;

		checkInputValidity();

		this.mResult = generateAutomaton(seed);
	}

	/*
	 * (non-Javadoc)
	 * 
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public TreeAutomatonBU<StringRankedLetter, String> getResult() {
		return this.mResult;
	}

	/**
	 * Adds states to the given preliminary automaton such that it has the desired
	 * amount of states and accepting states, specified by the current internal
	 * state of this object.<br>
	 * <br>
	 * Therefore the first <tt>k</tt> states are selected as accepting.
	 * 
	 * @param result
	 *            The automaton to add the states to
	 * @param numberToStateRepresentation
	 *            An array where the method is allowed to put the representation of
	 *            the generated states to. It needs to offer at least one entry for
	 *            each state.
	 */
	private void addStates(final TreeAutomatonBU<StringRankedLetter, String> result,
			final String[] numberToStateRepresentation) {
		final int numberOfAcceptingStates = densityToAbsolute(this.mAcceptanceDensity, this.mNumberOfStates);

		// Generate all states
		for (int i = 0; i < this.mNumberOfStates; i++) {
			// The representation of the generated state
			final String stateRepresentation = STATE_PREFIX + Integer.toString(i);

			// Determine if the state is accepting or not and add it to the automaton
			if (i < numberOfAcceptingStates) {
				result.addFinalState(stateRepresentation);
			} else {
				result.addState(stateRepresentation);
			}

			// Remember the representation
			numberToStateRepresentation[i] = stateRepresentation;
		}
	}

	/**
	 * Adds transitions and letters to the given preliminary automaton such that it
	 * matches the desired amount of letters and their corresponding densities,
	 * specified by the current internal state of this object.<br>
	 * <br>
	 * Therefore transitions are added arbitrary, source states and destination get
	 * selected randomly.
	 * 
	 * @param result
	 *            The automaton to add the states to
	 * @param numberToStateRepresentation
	 *            An array containing for each state its representation
	 * @param random
	 *            The random generator to use
	 * @throws IllegalStateException
	 *             If the generation detected a possible loop and aborted
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private void addTransitionsAndLetters(final TreeAutomatonBU<StringRankedLetter, String> result,
			final String[] numberToStateRepresentation, final Random random)
			throws IllegalStateException, AutomataOperationCanceledException {
		// Constant used for loop detection in source state generation
		final int maximalLoopCounter = LOOP_DETECTION_GIVE_UP_FACTOR * this.mNumberOfStates;

		// Iterate all ranks and create transitions for each rank separately
		final int highestRank = Math.min(this.mRankToNumberOfLetters.length, this.mRankToTransitionDensity.length) - 1;
		for (int rank = 0; rank <= highestRank; rank++) {
			// This boolean determines the source generation method to use, see the
			// documentation of the threshold
			final boolean useShuffleAllMethod = rank >= this.mNumberOfStates * USE_SHUFFLE_ALL_METHOD_THRESHOLD;
			final int numberOfLetters = this.mRankToNumberOfLetters[rank];
			final double transitionDensity = this.mRankToTransitionDensity[rank];

			// The amount of transitions per letter is given by applying the density to the
			// amount of states. If for example the density is 1.0 then each state will have
			// one transition with that letter.
			// However for ranks greater than 1 we must also take into account that
			// transitions will occupy multiple source states thus they are not available
			// anymore for other transitions with the same letter, else the automaton is not
			// deterministic anymore.
			// If for example a letter with rank 2 and 5 states are given then this letter
			// can only produce 2 transitions, after that there is no source state available
			// anymore that is not already involved in another transition of that letter.
			final int totalNumberOfTransitionsPerLetter;
			if (rank > 1) {
				totalNumberOfTransitionsPerLetter = Math.floorDiv(this.mNumberOfStates, rank);
			} else {
				totalNumberOfTransitionsPerLetter = this.mNumberOfStates;
			}
			// Apply the density to the total possible number of transitions per letter to
			// receive the absolute value
			final int numberOfTransitionsPerLetter = densityToAbsolute(transitionDensity,
					totalNumberOfTransitionsPerLetter);

			// Iterate each letter for transition generation
			for (int letterId = 0; letterId < numberOfLetters; letterId++) {
				// Preparations for the source state generation for transitions
				ArrayList<Integer> availableSourceStates = null;
				int nextAvailableSourceStatePointer = 0;
				HashSet<Integer> occupiedSourceStates = null;
				if (useShuffleAllMethod) {
					// We shuffle all states and later iteratively poll from them, this ensures that
					// every polled state is available and not used in another transition already.
					availableSourceStates = IntStream.range(0, this.mNumberOfStates).boxed()
							.collect(Collectors.toCollection(ArrayList::new));
					Collections.shuffle(availableSourceStates, random);
				} else {
					// We provide a set containing all already occupied states
					occupiedSourceStates = new HashSet<>(rank);
				}

				// The representation of the generated letter
				final String letterRepresentation = LETTER_PREFIX + rank + "_" + Integer.toString(letterId);
				final StringRankedLetter letter = new StringRankedLetter(letterRepresentation, rank);
				// Add the letter to the automaton
				result.addLetter(letter);

				// Generate transitions for this letter
				for (int transitionCounter = 0; transitionCounter < numberOfTransitionsPerLetter; transitionCounter++) {
					// Select a random state as destination
					final int destinationIndex = random.nextInt(this.mNumberOfStates);
					final String destinationState = numberToStateRepresentation[destinationIndex];

					// Select random available source states
					final List<String> sourceStates;
					if (rank == 0) {
						sourceStates = Collections.emptyList();
					} else {
						sourceStates = new ArrayList<>(rank);
					}

					// Generate the source states using the appropriate method
					while (sourceStates.size() < rank) {
						final int sourceStateIndex;
						if (useShuffleAllMethod) {
							if (availableSourceStates == null) {
								throw new AssertionError();
							}

							// Pull the next available source state and move the pointer forward
							sourceStateIndex = availableSourceStates.get(nextAvailableSourceStatePointer).intValue();
							nextAvailableSourceStatePointer++;
						} else {
							// Randomly select a candidate until one is available
							Integer sourceStateIndexCandidate;
							int loopCounter = 0;
							do {
								if (occupiedSourceStates == null) {
									throw new AssertionError();
								}
								if (loopCounter >= maximalLoopCounter) {
									throw new IllegalStateException(
											"Possible loop at source state generation detected, aborted.");
								}

								sourceStateIndexCandidate = Integer.valueOf(random.nextInt(this.mNumberOfStates));

								loopCounter++;
								// Continue until the candidate was not already occupied
							} while (occupiedSourceStates.contains(sourceStateIndexCandidate));
							sourceStateIndex = sourceStateIndexCandidate.intValue();
							occupiedSourceStates.add(sourceStateIndexCandidate);
						}

						// Add the given state to the list of source states
						final String sourceState = numberToStateRepresentation[sourceStateIndex];
						sourceStates.add(sourceState);
					}

					// Add the transition as rule to the automaton
					final TreeAutomatonRule<StringRankedLetter, String> rule = new TreeAutomatonRule<>(letter,
							sourceStates, destinationState);
					result.addRule(rule);
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (this.mProgressAwareTimer != null && !this.mProgressAwareTimer.continueProcessing()) {
					this.mLogger.debug("Stopped at creating transitions for letters");
					throw new AutomataOperationCanceledException(this.getClass());
				}
			}
		}
	}

	/**
	 * Checks whether the input of the operation is valid. Throws an exception if
	 * invalid. The method should be called right after initialization and before
	 * executing the generation.
	 * 
	 * @throws IllegalArgumentException
	 *             If an input is invalid
	 */
	private void checkInputValidity() throws IllegalArgumentException {
		// Number of states, check bounds
		if (this.mNumberOfStates < 0) {
			throw new IllegalArgumentException("Negative number of states.");
		}

		// Number of letters
		for (final int numberOfLetters : this.mRankToNumberOfLetters) {
			// Check bounds
			if (numberOfLetters < 0) {
				throw new IllegalArgumentException("Negative number of letters.");
			}
		}

		// Transition densities
		for (int i = 0; i < this.mRankToTransitionDensity.length; i++) {
			final double transitionDensity = this.mRankToTransitionDensity[i];
			// Check bounds
			if (transitionDensity < 0.0 || transitionDensity > 1.0) {
				throw new IllegalArgumentException("Illegal transition density.");
			}

			// Check conflict with number of letters
			if (transitionDensity > 0.0 && i < this.mRankToNumberOfLetters.length
					&& this.mRankToNumberOfLetters[i] <= 0) {
				throw new IllegalArgumentException("Impossible to have transitions without letters.");
			}
		}

		// Letter rank, check bounds
		final int highestRank = Math.min(this.mRankToNumberOfLetters.length, this.mRankToTransitionDensity.length);
		if (highestRank > this.mNumberOfStates - 1) {
			throw new IllegalArgumentException(
					"Impossible to have letters with a rank greater than the amount of states minus 1.");
		}

		// Acceptance, check bounds
		if (this.mAcceptanceDensity < 0.0 || this.mAcceptanceDensity > 1.0) {
			throw new IllegalArgumentException("Illegal acceptance density.");
		}
	}

	/**
	 * Generates the automaton with the given seed using the current internal state.
	 * 
	 * @param seed
	 *            The seed to use for generation
	 * @return The generated automaton representing the current internal state
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	private TreeAutomatonBU<StringRankedLetter, String> generateAutomaton(final long seed)
			throws AutomataOperationCanceledException {
		// Create the initial empty tree automaton
		final TreeAutomatonBU<StringRankedLetter, String> result = new TreeAutomatonBU<>();

		if (this.mNumberOfStates == 0) {
			// Empty automaton
			return result;
		}

		// The seeded random generator
		final Random random = new Random(seed);

		// Maps a number to each representation of a state
		final String[] numberToStateRepresentation = new String[this.mNumberOfStates];

		addStates(result, numberToStateRepresentation);

		// If operation was canceled, for example from the
		// Ultimate framework
		if (this.mProgressAwareTimer != null && !this.mProgressAwareTimer.continueProcessing()) {
			this.mLogger.debug("Stopped between creating states and transitions");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		addTransitionsAndLetters(result, numberToStateRepresentation, random);

		return result;
	}
	
	/**
	 * Demo usage of the random generator. Also used for debugging purpose.
	 * 
	 * @param args
	 *            Not supported
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate framework.
	 */
	public static void main(final String[] args) throws AutomataOperationCanceledException {
		// Dummy services
		final AutomataLibraryServices services = new AutomataLibraryServices(new ToolchainStorage());
		
		// Arguments for generation
		final int numberOfStates = 10;
		final int[] rankToNumberOfLetters = {2, 1, 3};
		final double[] rankToTransitionDensity = {0.1, 0.2, 0.5};
		final double acceptanceDensity = 0.2;
		
		final GetRandomDftaBU getRandomTree = new GetRandomDftaBU(services, numberOfStates, rankToNumberOfLetters, rankToTransitionDensity, acceptanceDensity);
		final TreeAutomatonBU<StringRankedLetter, String> tree = getRandomTree.getResult();
		
		// Output the generated tree
		System.out.println(tree);
	}
}
