/*
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2006 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.GeneralOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.StringFactory;

/**
 * Creates a random Buchi automaton.
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
 */
public class GetRandomBuchiAutomaton extends GeneralOperation<String, String> {
	private static final double ZERO = 0.0;
	private static final double ONE = 1.0;
	private static final double THOUSAND = 1_000;
	
	private static final String LETTER_PREFIX = "a";
	private static final String STATE_PREFIX = "q";
	
	private final NestedWordAutomaton<String, String> mResult;
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states
	 * @param numberOfLetters
	 *            number of letters
	 * @param transitionDensityPerMille
	 *            transition density (per mille)
	 * @param acceptanceDensityPerMille
	 *            acceptance density (per mille)
	 */
	public GetRandomBuchiAutomaton(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfLetters, final int transitionDensityPerMille, final int acceptanceDensityPerMille) {
		this(services, numberOfStates, numberOfLetters, transitionDensityPerMille / THOUSAND,
				acceptanceDensityPerMille / THOUSAND);
	}
	
	/**
	 * Constructor.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param numberOfStates
	 *            number of states {@code (>= 0)}
	 * @param numberOfLetters
	 *            number of letters {@code (>= 0)}
	 * @param transitionDensity
	 *            transition density {@code (>= 0)}
	 * @param acceptanceDensity
	 *            acceptance density {@code (0 <= x <= 1)}
	 */
	@SuppressWarnings("squid:S1244")
	public GetRandomBuchiAutomaton(final AutomataLibraryServices services, final int numberOfStates,
			final int numberOfLetters, final double transitionDensity, final double acceptanceDensity) {
		super(services);
		
		// check for valid inputs
		if (numberOfStates < ZERO) {
			throw new IllegalArgumentException("Negative number of states.");
		}
		if (numberOfLetters < ZERO) {
			throw new IllegalArgumentException("Negative number of letters.");
		}
		if (numberOfLetters == ZERO && transitionDensity > ZERO) {
			throw new IllegalArgumentException("Impossible to have transitions without letters.");
		}
		if (transitionDensity < ZERO) {
			throw new IllegalArgumentException("Negative transition density.");
		}
		if (acceptanceDensity < ZERO || acceptanceDensity > ONE) {
			throw new IllegalArgumentException("Illegal acceptance density.");
		}
		
		// generate result
		mResult = generateAutomaton(numberOfStates, numberOfLetters, transitionDensity, acceptanceDensity);
	}
	
	@Override
	public INestedWordAutomaton<String, String> getResult() {
		return mResult;
	}
	
	private NestedWordAutomaton<String, String> generateAutomaton(final int numberOfStates, final int numberOfLetters,
			final double transitionDensity, final double acceptanceDensity) {
		// alphabet (filled later)
		final Set<String> alphabetAsSet = new HashSet<>(numberOfLetters);
		
		// create raw automaton
		final NestedWordAutomaton<String, String> result = new NestedWordAutomaton<>(mServices, alphabetAsSet,
				Collections.emptySet(), Collections.emptySet(), new StringFactory());
		
		if (numberOfStates == 0) {
			// empty automaton
			return result;
		}
		
		// random generator
		final Random rand = new Random();
		
		// data structure
		final String[] int2state = new String[numberOfStates];
		
		/*
		 * add states
		 * 
		 * We just make the first k states accepting and one of the states initial.
		 * The actual randomization comes with the transitions.
		 */
		final int initialStateIndex = rand.nextInt(numberOfStates);
		final int numberOfAcceptingStates = densityToAbsolute(acceptanceDensity, numberOfStates);
		for (int i = 0; i < numberOfStates; ++i) {
			// state names start at 0
			final String state = STATE_PREFIX + Integer.toString(i);
			
			result.addState(i == initialStateIndex, i < numberOfAcceptingStates, state);
			int2state[i] = state;
		}
		
		// data structure
		final boolean[][] added = new boolean[numberOfStates][numberOfStates];
		
		/*
		 * add transitions
		 * 
		 * For each letter add the specified number of transitions. Transitions are distributed arbitrarily (i.e., there
		 * can be states with no respective transitions and others with several transitions).
		 */
		final int numberOfTransitionsPerLetter = densityToAbsolute(transitionDensity, numberOfStates);
		for (int i = 0; i < numberOfLetters; ++i) {
			// create new letter (names start at 0)
			final String letter = LETTER_PREFIX + Integer.toString(i);
			
			// add letter to alphabet
			alphabetAsSet.add(letter);
			
			// data structure preparation
			if (i == 0) {
				// initialize data structure
				for (int j = 0; j < numberOfStates; ++j) {
					added[j] = new boolean[numberOfStates];
				}
			} else {
				// refresh data structure
				for (int j = 0; j < numberOfStates; ++j) {
					Arrays.fill(added[j], false);
				}
			}
			
			// add as many transitions with the letter as required
			addTransitionsGivenLetter(result, rand, int2state, added, letter, numberOfStates,
					numberOfTransitionsPerLetter);
		}
		return result;
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
	 * Implementation details:<br>
	 * Adding transitions happens in a loop with random number generation. It is possible that this loop never
	 * terminates for bad choices. However, the probability for this to happen is zero. If this is ever a problem in
	 * practice, one can think of a different implementation where the numbers are drawn from the available ones; this
	 * is less efficient in most cases but needs no loop.
	 */
	private static void addTransitionsGivenLetter(final NestedWordAutomaton<String, String> result, final Random rand,
			final String[] int2state, final boolean[][] added, final String letter, final int numberOfStates,
			final int numberOfTransitions) {
		// add transitions
		for (int transition = 0; transition < numberOfTransitions; ++transition) {
			// add a new transition
			do {
				final int i = rand.nextInt(numberOfStates);
				final int j = rand.nextInt(numberOfStates);
				if (!added[i][j]) {
					// transition is new, add it
					result.addInternalTransition(int2state[i], letter, int2state[j]);
					added[i][j] = true;
					break;
				}
			} while (true);
		}
	}
}
