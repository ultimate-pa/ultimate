/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;

/**
 * Creates a random nested word automaton.
 * <p>
 * We use a generalization of the <i>Tabakov-Vardi</i> random model.<br>
 * See either of
 * <ul>
 * <li><i>2005 Tabakov, Vardi - Experimental evaluation of classical automata constructions</i></li>
 * <li><i>2007 Tabakov, Vardi - Model checking Buchi specifications</i></li>
 * </ul>
 * for details. The generalization is that we do not require the initial state to be accepting and that we allow an
 * arbitrary number of letters.
 * <p>
 * Implementation details: See
 * {@link #addTransitionsGivenLetter(NestedWordAutomaton, Random, String[], boolean[][], String, int, int)
 * addTransitionsGivenLetter()}.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @author Daniel Tischner {@literal <zabuza.dev@gmail.com>}
 */
public class GetRandomNwaTv extends GeneralOperation<String, String, IStateFactory<String>> {
	private static final double HUNDRED = 100;
	private static final String LETTER_CALL_PREFIX = "c";
	private static final String LETTER_INTERNAL_PREFIX = "a";
	private static final String LETTER_RETURN_PREFIX = "r";

	private static final int MODE_CALL = 1;
	private static final int MODE_INTERNAL = 0;
	private static final int MODE_RETURN = 2;
	private static final double ONE = 1.0;

	private static final String STATE_PREFIX = "q";
	private static final double ZERO = 0.0;
	private static final int ZERO_INT = 0;
	private static final long DEFAULT_SEED = 0;

	private final double mAcceptanceDensity;
	private final double mCallTransitionDensity;
	private final double mHierarchicalPredecessorDensity;
	private final double mInternalTransitionDensity;
	private final int mNumberOfCallLetters;
	private final int mNumberOfInternalLetters;
	private final int mNumberOfReturnLetters;
	private final int mNumberOfStates;
	private final NestedWordAutomaton<String, String> mResult;
	private final double mReturnTransitionDensity;

	/**
	 * Constructor of a finite automaton for the {@code TestFileInterpreter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states
	 * @param numberOfInternalLetters
	 *            number of letters
	 * @param transitionDensityPercent
	 *            (internal) transition density (in percent)
	 * @param acceptanceDensityPercent
	 *            acceptance density (in percent)
	 */
	public GetRandomNwaTv(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfInternalLetters, final int transitionDensityPercent, final int acceptanceDensityPercent) {
		this(services, numberOfStates, numberOfInternalLetters, transitionDensityPercent / HUNDRED,
				acceptanceDensityPercent / HUNDRED, DEFAULT_SEED);
	}

	/**
	 * Constructor of a finite automaton.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states {@code (>= 0)}
	 * @param numberOfInternalLetters
	 *            number of letters {@code (>= 0)}
	 * @param transitionDensity
	 *            (internal) transition density {@code (>= 0)}
	 * @param acceptanceDensity
	 *            acceptance density {@code (0 <= x <= 1)}
	 */
	@SuppressWarnings("squid:S1244")
	public GetRandomNwaTv(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfInternalLetters, final double transitionDensity, final double acceptanceDensity,
			final long seed) {
		this(services, numberOfStates, numberOfInternalLetters, ZERO_INT, ZERO_INT, transitionDensity, ZERO, ZERO, ZERO,
				acceptanceDensity, seed);
	}

	/**
	 * Constructor of a nested word automaton for the {@code TestFileInterpreter}.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states
	 * @param numberOfInternalLetters
	 *            number of internal letters
	 * @param numberOfCallLetters
	 *            number of call letters
	 * @param numberOfReturnLetters
	 *            number of return letters
	 * @param internalTransitionDensityPercent
	 *            internal transition density (in percent)
	 * @param callTransitionDensityPercent
	 *            call transition density (in percent)
	 * @param returnTransitionDensityPercent
	 *            return transition density (in percent)
	 * @param hierarchicalPredecessorDensityPercent
	 *            hierarchical predecessor density for return transitions (per mille)
	 * @param acceptanceDensityPercent
	 *            acceptance density (in percent)
	 */
	public GetRandomNwaTv(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfInternalLetters, final int numberOfCallLetters, final int numberOfReturnLetters,
			final int internalTransitionDensityPercent, final int callTransitionDensityPercent,
			final int returnTransitionDensityPercent, final int hierarchicalPredecessorDensityPercent,
			final int acceptanceDensityPercent) {
		this(services, numberOfStates, numberOfInternalLetters, numberOfCallLetters, numberOfReturnLetters,
				internalTransitionDensityPercent / HUNDRED, callTransitionDensityPercent / HUNDRED,
				returnTransitionDensityPercent / HUNDRED, hierarchicalPredecessorDensityPercent / HUNDRED,
				acceptanceDensityPercent / HUNDRED, DEFAULT_SEED);
	}

	/**
	 * Constructor of a nested word automaton.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states {@code (>= 0)}
	 * @param numberOfInternalLetters
	 *            number of internal letters {@code (>= 0)}
	 * @param numberOfCallLetters
	 *            number of return letters {@code (>= 0)}
	 * @param numberOfReturnLetters
	 *            number of return letters {@code (>= 0)}
	 * @param internalTransitionDensity
	 *            internal transition density {@code (>= 0)}
	 * @param callTransitionDensity
	 *            call transition density {@code (>= 0)}
	 * @param returnTransitionDensity
	 *            return transition density {@code (>= 0)}
	 * @param hierarchicalPredecessorDensity
	 *            hierarchical predecessor density for return transitions
	 * @param acceptanceDensity
	 *            acceptance density {@code (0 <= x <= 1)}
	 * @param seed
	 *            The seed to use for random automaton generation, if present
	 */
	public GetRandomNwaTv(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfInternalLetters, final int numberOfCallLetters, final int numberOfReturnLetters,
			final double internalTransitionDensity, final double callTransitionDensity,
			final double returnTransitionDensity, final double hierarchicalPredecessorDensity,
			final double acceptanceDensity, final long seed) {
		super(services);
		mNumberOfStates = numberOfStates;
		mNumberOfInternalLetters = numberOfInternalLetters;
		mNumberOfCallLetters = numberOfCallLetters;
		mNumberOfReturnLetters = numberOfReturnLetters;
		mInternalTransitionDensity = internalTransitionDensity;
		mCallTransitionDensity = callTransitionDensity;
		mReturnTransitionDensity = returnTransitionDensity;
		mHierarchicalPredecessorDensity = hierarchicalPredecessorDensity;
		mAcceptanceDensity = acceptanceDensity;

		checkInputValidity();

		mResult = generateAutomaton(seed);
	}

	@Override
	public INestedWordAutomaton<String, String> getResult() {
		return mResult;
	}

	@SuppressWarnings("squid:S1244")
	private static int densityToAbsolute(final double density, final int numberOfStates) {
		final int resultRaw = (int) (density * numberOfStates);
		final int result;
		if (resultRaw > 0) {
			result = resultRaw;
		} else {
			// make result zero only if the density is precisely zero
			result = (density == ZERO) ? 0 : 1;
		}
		return result;
	}

	/**
	 * Adds states.
	 * <p>
	 * We just make the first k states accepting and one of the states initial. The actual randomization comes with the
	 * transitions.
	 */
	private void addStates(final NestedWordAutomaton<String, String> result, final String[] int2state,
			final Random rand) {
		final int initialStateIndex = rand.nextInt(mNumberOfStates);
		final int numberOfAcceptingStates = densityToAbsolute(mAcceptanceDensity, mNumberOfStates);
		for (int i = 0; i < mNumberOfStates; ++i) {
			// state names start at 0
			final String state = STATE_PREFIX + Integer.toString(i);

			result.addState(i == initialStateIndex, i < numberOfAcceptingStates, state);
			int2state[i] = state;
		}
	}

	/**
	 * Adds transitions.
	 * <p>
	 * For each letter add the specified number of transitions. Transitions are distributed arbitrarily (i.e., there can
	 * be states with no respective transitions and others with several transitions).
	 */
	private void addTransitions(final Set<String> alphabet, final NestedWordAutomaton<String, String> result,
			final Random rand, final String[] int2state, final int mode) {
		final int numberOfLetters;
		final int numberOfTransitionsPerLetter;
		final String letterPrefix;
		switch (mode) {
			case MODE_INTERNAL:
				numberOfLetters = mNumberOfInternalLetters;
				numberOfTransitionsPerLetter = densityToAbsolute(mInternalTransitionDensity, mNumberOfStates);
				letterPrefix = LETTER_INTERNAL_PREFIX;
				break;
			case MODE_CALL:
				numberOfLetters = mNumberOfCallLetters;
				numberOfTransitionsPerLetter = densityToAbsolute(mCallTransitionDensity, mNumberOfStates);
				letterPrefix = LETTER_CALL_PREFIX;
				break;
			case MODE_RETURN:
				numberOfLetters = mNumberOfReturnLetters;
				numberOfTransitionsPerLetter = densityToAbsolute(mReturnTransitionDensity, mNumberOfStates);
				letterPrefix = LETTER_RETURN_PREFIX;
				break;
			default:
				throw new IllegalArgumentException();
		}

		// data structure
		final boolean[][] added = new boolean[mNumberOfStates][mNumberOfStates];

		for (int i = 0; i < numberOfLetters; ++i) {
			// create new letter (names start at 0)
			final String letter = letterPrefix + Integer.toString(i);

			// add letter to alphabet
			alphabet.add(letter);

			// data structure preparation
			if (i == 0) {
				// initialize data structure
				for (int j = 0; j < mNumberOfStates; ++j) {
					added[j] = new boolean[mNumberOfStates];
				}
			} else {
				// refresh data structure
				for (int j = 0; j < mNumberOfStates; ++j) {
					Arrays.fill(added[j], false);
				}
			}

			// add as many transitions with the letter as required
			addTransitionsGivenLetter(result, rand, int2state, added, letter, numberOfTransitionsPerLetter, mode);
		}
	}

	/**
	 * Implementation detail:<br>
	 * Adding transitions happens in a loop with random number generation. It is possible that this loop never
	 * terminates for bad choices. However, the probability for this to happen is zero. If this is ever a problem in
	 * practice, one can think of a different implementation where the numbers are drawn from the available ones; this
	 * is less efficient in most cases but needs no loop.
	 */
	private void addTransitionsGivenLetter(final NestedWordAutomaton<String, String> result, final Random rand,
			final String[] int2state, final boolean[][] added, final String letter, final int numberOfTransitions,
			final int mode) {
		// add transitions
		for (int transition = 0; transition < numberOfTransitions; ++transition) {
			// add a new transition
			do {
				final int i = rand.nextInt(mNumberOfStates);
				final int j = rand.nextInt(mNumberOfStates);
				if (!added[i][j]) {
					// transition is new, add it
					addTransitionToAutomaton(result, int2state, letter, mode, i, j, rand);
					added[i][j] = true;
					break;
				}
			} while (true);
		}
	}

	/**
	 * Dispatches the different transition types.
	 * <p>
	 * For return transitions we additionally choose random hierarchical predecessors.
	 */
	private void addTransitionToAutomaton(final NestedWordAutomaton<String, String> result, final String[] int2state,
			final String letter, final int mode, final int pred, final int succ, final Random rand) {
		switch (mode) {
			case MODE_INTERNAL:
				result.addInternalTransition(int2state[pred], letter, int2state[succ]);
				break;
			case MODE_CALL:
				result.addCallTransition(int2state[pred], letter, int2state[succ]);
				break;
			case MODE_RETURN:
				for (final int hier : getRandomHierarchicalPredecessors(rand)) {
					result.addReturnTransition(int2state[pred], int2state[hier], letter, int2state[succ]);
				}
				break;
			default:
				throw new IllegalArgumentException();
		}
	}

	@SuppressWarnings({ "squid:S1244", "squid:MethodCyclomaticComplexity" })
	private void checkInputValidity() {
		// check for valid inputs
		if (mNumberOfStates < ZERO_INT) {
			throw new IllegalArgumentException("Negative number of states.");
		}
		if (mNumberOfInternalLetters < ZERO_INT) {
			throw new IllegalArgumentException("Negative number of letters.");
		}
		if (mNumberOfInternalLetters == ZERO_INT && mInternalTransitionDensity > ZERO) {
			throw new IllegalArgumentException("Impossible to have internal transitions without letters.");
		}
		if (mNumberOfCallLetters == ZERO_INT && mCallTransitionDensity > ZERO) {
			throw new IllegalArgumentException("Impossible to have call transitions without letters.");
		}
		if (mNumberOfReturnLetters == ZERO_INT && mReturnTransitionDensity > ZERO) {
			throw new IllegalArgumentException("Impossible to have return transitions without letters.");
		}
		if (mInternalTransitionDensity < ZERO || mCallTransitionDensity < ZERO || mReturnTransitionDensity < ZERO) {
			throw new IllegalArgumentException("Negative transition density.");
		}
		if (mHierarchicalPredecessorDensity < ZERO) {
			throw new IllegalArgumentException("Negative hierarchical predecessor density.");
		}
		if (mReturnTransitionDensity > ZERO ^ mHierarchicalPredecessorDensity > ZERO) {
			throw new IllegalArgumentException("Inconsistent return transition and hierarchical predecessor density.");
		}
		if (mAcceptanceDensity < ZERO || mAcceptanceDensity > ONE) {
			throw new IllegalArgumentException("Illegal acceptance density.");
		}
	}

	private NestedWordAutomaton<String, String> generateAutomaton(final long seed) {
		// alphabets (filled later)
		final Set<String> internalAlphabet = new HashSet<>(mNumberOfInternalLetters);
		final Set<String> callAlphabet = new HashSet<>(mNumberOfInternalLetters);
		final Set<String> returnAlphabet = new HashSet<>(mNumberOfInternalLetters);

		// create raw automaton
		final NestedWordAutomaton<String, String> result = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(internalAlphabet,
				callAlphabet, returnAlphabet), new StringFactory());

		if (mNumberOfStates == 0) {
			// empty automaton
			return result;
		}

		// random generator
		final Random rand = new Random(seed);

		// data structure
		final String[] int2state = new String[mNumberOfStates];

		addStates(result, int2state, rand);

		addTransitions(internalAlphabet, result, rand, int2state, MODE_INTERNAL);
		addTransitions(callAlphabet, result, rand, int2state, MODE_CALL);
		addTransitions(returnAlphabet, result, rand, int2state, MODE_RETURN);

		return result;
	}

	private Iterable<Integer> getRandomHierarchicalPredecessors(final Random rand) {
		final Set<Integer> result = new HashSet<>();
		final int numberOfAcceptingStates = densityToAbsolute(mHierarchicalPredecessorDensity, mNumberOfStates);
		while (result.size() < numberOfAcceptingStates) {
			result.add(Integer.valueOf(rand.nextInt(mNumberOfStates)));
		}
		return result;
	}
}
