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
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.tree.StringRankedLetter;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonBU;
import de.uni_freiburg.informatik.ultimate.automata.tree.TreeAutomatonRule;

/**
 * Creates a random deterministic or non-deterministic finite bottom-up tree
 * automaton (DFTA-BU). Note that the generation is not uniform.
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
abstract class AGetRandomFtaBU extends GeneralOperation<StringRankedLetter, String, IStateFactory<String>> {
	/**
	 * Prefix that is used for letters.
	 */
	private static final String LETTER_PREFIX = "a";
	/**
	 * Prefix that is used for states.
	 */
	private static final String STATE_PREFIX = "q";

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
	protected static int densityToAbsolute(final double density, final int numberOfTotal) {
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
	 * Whether the generator should only generate deterministic tree automata. If
	 * <tt>true</tt> then only deterministic tree automata will get generated
	 * whereas <tt>false</tt> can also lead to non-deterministic automata.
	 */
	private final boolean mGenerateOnlyDeterministic;
	/**
	 * The number of states {@code (>= 0)}.
	 */
	private final int mNumberOfStates;
	/**
	 * Each index stands for the rank of a letter. The value stored at an index
	 * represents the amount of letters with that rank should be generated. Each
	 * value is {@code >= 0}.
	 */
	private final int[] mRankToNumberOfLetters;
	/**
	 * Each index stands for the rank of a letter. The value stored at an index
	 * represents the amount of transitions per letter of that rank. The number of
	 * transitions of nullary letters specify the amount of initial states.
	 */
	protected final int[] mRankToNumberOfTransitionsPerLetter;
	/**
	 * The resulting tree automaton after generation.
	 */
	private TreeAutomatonBU<StringRankedLetter, String> mResult = null;
	/**
	 * The seed to use for random automaton generation.
	 */
	private long mSeed;

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
	 * @param rankToNumberOfTransitionsPerLetter
	 *            Each index stands for the rank of a letter. The value stored at an
	 *            index represents the amount of transitions per letter of that rank
	 *            {@code (>= 0)}. The number of transitions of nullary letters
	 *            specify the amount of initial states thus if initial states are
	 *            desired <code>rankToNumberOfTransitionsPerLetter[0]</code> should
	 *            be set to a value greater than <tt>zero</tt>. Also note that the
	 *            number must be below the maximal possible amount of transitions
	 *            which is given by {@code states^rank} (if deterministic) or
	 *            {@code states^(rank + 1)} if non-deterministic. For efficiency
	 *            reasons this object will not check validity for those upper
	 *            bounds. If setting higher values it is possible that this object
	 *            never terminates the generation process.
	 * @param acceptanceDensity
	 *            The acceptance density {@code (0 <= x <= 1)}. If <tt>1</tt> then
	 *            all states are accepting, if <tt>0</tt> then no state is
	 *            accepting.
	 * @param generateOnlyDeterministic
	 *            Whether the generator should only generate deterministic tree
	 *            automata. If <tt>true</tt> then only deterministic tree automata
	 *            will get generated whereas <tt>false</tt> can also lead to
	 *            non-deterministic automata.
	 * @param seed
	 *            The seed to use for random automaton generation.
	 */
	public AGetRandomFtaBU(final AutomataLibraryServices services, final int numberOfStates,
			final int[] rankToNumberOfLetters, final int[] rankToNumberOfTransitionsPerLetter,
			final double acceptanceDensity, final boolean generateOnlyDeterministic, final long seed) {
		super(services);

		this.mNumberOfStates = numberOfStates;
		this.mRankToNumberOfLetters = rankToNumberOfLetters;
		this.mRankToNumberOfTransitionsPerLetter = rankToNumberOfTransitionsPerLetter;
		this.mAcceptanceDensity = acceptanceDensity;
		this.mGenerateOnlyDeterministic = generateOnlyDeterministic;

		this.mSeed = seed;
	}

	/*
	 * (non-Javadoc)
	 *
	 * @see de.uni_freiburg.informatik.ultimate.automata.IOperation#getResult()
	 */
	@Override
	public TreeAutomatonBU<StringRankedLetter, String> getResult() {
		assert new isDetereministic<>(mServices, mResult).getResult();
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
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to generate states");
		}

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
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting to generate transitions and letters");
		}

		// Iterate all ranks and create transitions for each rank separately
		final int highestRank = Math.min(this.mRankToNumberOfLetters.length,
				this.mRankToNumberOfTransitionsPerLetter.length) - 1;
		for (int rank = 0; rank <= highestRank; rank++) {
			if (this.mLogger.isDebugEnabled()) {
				this.mLogger.debug("Generating transitions and letters for rank " + rank);
			}

			final int numberOfLetters = this.mRankToNumberOfLetters[rank];
			final int numberOfTransitionsPerLetter = this.mRankToNumberOfTransitionsPerLetter[rank];

			// Iterate each letter for transition generation
			for (int letterId = 0; letterId < numberOfLetters; letterId++) {
				// The representation of the generated letter
				final String letterRepresentation = LETTER_PREFIX + rank + "_" + Integer.toString(letterId);
				final StringRankedLetter letter = new StringRankedLetter(letterRepresentation, rank);
				// Add the letter to the automaton
				result.addLetter(letter);

				// Preparations for the source state generation for transitions
				// We provide a set containing all already occupied state combinations or rules
				// depending on the generation mode
				final Set<List<Integer>> occupiedSourceStateCombinations;
				final Set<TreeAutomatonRule<StringRankedLetter, String>> occupiedRules;
				if (this.mGenerateOnlyDeterministic) {
					occupiedSourceStateCombinations = new HashSet<>(numberOfTransitionsPerLetter);
					occupiedRules = Collections.emptySet();
				} else {
					// For non-deterministic
					occupiedSourceStateCombinations = Collections.emptySet();
					occupiedRules = new HashSet<>(numberOfTransitionsPerLetter);
				}

				// Generate transitions for this letter
				int transitionCounter = 0;
				while (transitionCounter < numberOfTransitionsPerLetter) {
					// Select a random state as destination
					final int destinationIndex = random.nextInt(this.mNumberOfStates);
					final String destinationState = numberToStateRepresentation[destinationIndex];

					// Select random available source state combinations and repeat until a
					// combination that was not already used before was found
					List<Integer> sourceStateIndices;
					do {
						if (rank == 0) {
							// Empty source states are always valid and available
							sourceStateIndices = Collections.emptyList();
							break;
						}

						// Generate a random combination of source states and add them to the list
						sourceStateIndices = random.ints(rank, 0, this.mNumberOfStates).sequential().boxed()
								.collect(Collectors.toCollection(ArrayList::new));

						// Check whether the combination was already used before
					} while (occupiedSourceStateCombinations.contains(sourceStateIndices));

					// The combination is available and thus can be used
					if (this.mGenerateOnlyDeterministic) {
						occupiedSourceStateCombinations.add(sourceStateIndices);
					}
					// Convert the source state indices to their corresponding representations
					final ArrayList<String> sourceStates = sourceStateIndices.stream().sequential()
							.map(sourceStateIndex -> numberToStateRepresentation[sourceStateIndex.intValue()])
							.collect(Collectors.toCollection(ArrayList::new));

					// Create the corresponding rule
					final TreeAutomatonRule<StringRankedLetter, String> rule = new TreeAutomatonRule<>(letter,
							sourceStates, destinationState);
					// If non-deterministic we also need to ensure that the rule was not generated
					// before already
					if (!this.mGenerateOnlyDeterministic) {
						if (occupiedRules.contains(rule)) {
							// Try to generate a transition for this letter again
							continue;
						}
						// The rule is available and thus can be used
						occupiedRules.add(rule);
					}

					// Add the rule to the automaton and advance in transition generation
					result.addRule(rule);
					transitionCounter++;
				}

				// If operation was canceled, for example from the
				// Ultimate framework
				if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
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
	protected void checkInputValidity() throws IllegalArgumentException {
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

		// Number of transitions per letter
		for (int i = 0; i < this.mRankToNumberOfTransitionsPerLetter.length; i++) {
			final int numberOfTransitionsPerLetter = this.mRankToNumberOfTransitionsPerLetter[i];
			// Check bounds
			if (numberOfTransitionsPerLetter < 0) {
				throw new IllegalArgumentException("Negative number of transitions per letter.");
			}

			// Check conflict with number of letters
			if (numberOfTransitionsPerLetter > 0 && i < this.mRankToNumberOfLetters.length
					&& this.mRankToNumberOfLetters[i] <= 0) {
				throw new IllegalArgumentException("Impossible to have transitions without letters.");
			}
		}

		// Letter rank, check bounds
		final int highestRank = Math.min(this.mRankToNumberOfLetters.length,
				this.mRankToNumberOfTransitionsPerLetter.length);
		if (highestRank > this.mNumberOfStates) {
			throw new IllegalArgumentException(
					"Impossible to have letters with a rank greater than the amount of states.");
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
	protected TreeAutomatonBU<StringRankedLetter, String> generateAutomaton(final long seed)
			throws AutomataOperationCanceledException {
		if (this.mLogger.isDebugEnabled()) {
			this.mLogger.debug("Starting generation using the seed " + seed);
		}

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
		if (this.mServices.getProgressAwareTimer() != null && isCancellationRequested()) {
			this.mLogger.debug("Stopped between creating states and transitions");
			throw new AutomataOperationCanceledException(this.getClass());
		}

		addTransitionsAndLetters(result, numberToStateRepresentation, random);

		return result;
	}

	/**
	 * Starts the generation of the random tree automaton. After the method has
	 * terminated the result can be accessed by using {@link #getResult()}.
	 *
	 * @throws AutomataOperationCanceledException
	 *             If the operation was canceled, for example from the Ultimate
	 *             framework.
	 */
	protected void startGeneration() throws AutomataOperationCanceledException {
		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(startMessage());
		}

		checkInputValidity();
		this.mResult = generateAutomaton(this.mSeed);
		// Deterministically change the seed for the next generation
		this.mSeed++;

		if (this.mLogger.isInfoEnabled()) {
			this.mLogger.info(exitMessage());
		}
	}
}
