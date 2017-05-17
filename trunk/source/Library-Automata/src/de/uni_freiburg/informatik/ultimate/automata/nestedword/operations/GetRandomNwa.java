/*
 * Copyright (C) 2012-2015 Fabian Reiter
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2009-2015 University of Freiburg
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

import java.text.MessageFormat;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
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
 * Generates a random connected nested word automaton.
 * <p>
 * Here connected means that every state is reachable from the (unique) initial state.
 * 
 * @author Fabian Reiter
 */
public final class GetRandomNwa extends GeneralOperation<String, String, IStateFactory<String>> {
	private static final long DEFAULT_SEED = 0;

	private final Random mRandom;
	private final INestedWordAutomaton<String, String> mResult;

	private final int mAlphabetSize;
	private final int mSize;
	private final double mInternalTransitionDensity;
	private final double mCallTransitionDensity;
	private final double mReturnTransitionDensity;
	private final double mAcceptanceDensity;

	/**
	 * Constructor with {@code int} values.
	 * <p>
	 * Since the parser does not support the {@code double} type, the inputs are values in per mille (divided by 1000).
	 * 
	 * @param services
	 *            Ultimate services
	 * @param alphabetSize
	 *            alphabet size
	 * @param size
	 *            number of states
	 * @param internalTransitionDensity
	 *            internal transition density (per mille)
	 * @param callTransitionProbability
	 *            call transition density (per mille)
	 * @param returnTransitionProbability
	 *            return transition density (per mille)
	 * @param acceptanceDensity
	 *            acceptance density (per mille)
	 * @see {@link #generateAutomaton(int, int, double, double, double, double)}.
	 */
	public GetRandomNwa(final AutomataLibraryServices services, final int alphabetSize, final int size,
			final int internalTransitionDensity, final int callTransitionProbability,
			final int returnTransitionProbability, final int acceptanceDensity) {
		this(services, alphabetSize, size, internalTransitionDensity / 1_000D, callTransitionProbability / 1_000D,
				returnTransitionProbability / 1_000D, acceptanceDensity / 1_000D, DEFAULT_SEED);
	}

	/**
	 * Constructor with {@code double} values.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param alphabetSize
	 *            alphabet size
	 * @param size
	 *            number of states
	 * @param internalTransitionDensity
	 *            internal transition density
	 * @param callTransitionProbability
	 *            call transition density
	 * @param returnTransitionProbability
	 *            return transition density
	 * @param acceptanceDensity
	 *            acceptance density
	 * @param seed
	 *            seed
	 * @see {@link #generateAutomaton(int, int, double, double, double, double)}.
	 */
	public GetRandomNwa(final AutomataLibraryServices services, final int alphabetSize, final int size,
			final double internalTransitionDensity, final double callTransitionProbability,
			final double returnTransitionProbability, final double acceptanceDensity, final long seed) {
		super(services);
		mRandom = new Random(seed);
		mAlphabetSize = alphabetSize;
		mSize = size;
		mInternalTransitionDensity = internalTransitionDensity;
		mCallTransitionDensity = callTransitionProbability;
		mReturnTransitionDensity = returnTransitionProbability;
		mAcceptanceDensity = acceptanceDensity;
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		mResult = generateAutomaton();
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String operationName() {
		return "GetRandomNwa";
	}

	@Override
	public String startMessage() {
		return MessageFormat.format(
				"Start {0}. Alphabet size {1} Number of states {2} "
						+ "Density internal transition {3} Density call transition {4} Density return transition {5} "
						+ "Acceptance density {6}",
				operationName(), mAlphabetSize, mSize, mInternalTransitionDensity, mCallTransitionDensity,
				mReturnTransitionDensity, mAcceptanceDensity);
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". Result " + mResult.sizeInformation() + '.';
	}

	@Override
	public INestedWordAutomaton<String, String> getResult() {
		return mResult;
	}

	/**
	 * Generates the automaton.
	 * 
	 * @param mAlphabetSize
	 *            number of letters of the alphabet
	 * @param mSize
	 *            number of states of the automaton
	 * @param mInternalTransitionDensity
	 *            fraction of possible internal transitions that actually exist in the automaton (number between 0 and
	 *            1)
	 * @param mCallTransitionDensity
	 *            fraction of possible call transitions that actually exist in the automaton (number between 0 and 1)
	 * @param mReturnTransitionDensity
	 *            fraction of possible return transitions that actually exist in the automaton (number between 0 and 1)
	 * @param mAcceptanceDensity
	 *            fraction of states that are accepting (number between 0 and 1)
	 * @return a randomly generated NFA that fulfills the given specification
	 */
	private INestedWordAutomaton<String, String> generateAutomaton() {
		// --------------------------------------------------------------------
		// Check user input and compute num. of transitions & accepting states.
		//
		checkUserInput();

		final int maxNumOfTransitions = mSize * mAlphabetSize * mSize;
		final int numOfTransitions = (int) Math.round(mInternalTransitionDensity * maxNumOfTransitions);
		if ((numOfTransitions < mSize - 1) && (mLogger.isWarnEnabled())) {
			mLogger.warn("You specified density " + mInternalTransitionDensity + " for internal transition. "
					+ "This is not sufficient to connect all states with internal transitions.");
		}

		final int numOfAccStates = (int) Math.round(mAcceptanceDensity * mSize);

		// --------------------------------------------------------------------
		// Create state and letter objects and store them in two lists.
		//
		final List<String> num2State = new ArrayList<>(mSize);
		for (int i = 0; i < mSize; ++i) {
			num2State.add("q" + i);
		}
		final String initialState = num2State.get(0); // q₀

		final List<String> num2Letter = new ArrayList<>(mAlphabetSize);
		for (int i = 0; i < mAlphabetSize; ++i) {
			num2Letter.add("a" + i);
		}

		// --------------------------------------------------------------------
		// Create the result automaton.
		// If both, callTransitionProbability and returnTransitionProbability
		// are 0 we set callAlphabet and returnAlphabet to null.
		//
		NestedWordAutomaton<String, String> result;
		@SuppressWarnings("squid:S1244")
		final boolean isFiniteAutomaton = mCallTransitionDensity == 0D && mReturnTransitionDensity == 0D;
		if (isFiniteAutomaton) {
			result = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(new HashSet<>(num2Letter)), new StringFactory());
		} else {
			result = new NestedWordAutomaton<>(mServices, new VpAlphabet<>(new HashSet<>(num2Letter), new HashSet<>(num2Letter),
					new HashSet<>(num2Letter)), new StringFactory());
		}

		// --------------------------------------------------------------------
		// Add the states to the result automaton.
		//
		addStates(numOfAccStates, num2State, initialState, result);

		// --------------------------------------------------------------------
		// add internal transitions
		addInternalTransitions(maxNumOfTransitions, numOfTransitions, num2State, num2Letter, result);

		// --------------------------------------------------------------------
		// add call/return transitions

		if (!isFiniteAutomaton) {
			addCallReturnTransitions(num2State, num2Letter, result);
		}

		return result;
	}

	private void checkUserInput() {
		if (mSize <= 0) {
			throw new IllegalArgumentException("Automaton size must be strictly positive.");
		}
		if (mAlphabetSize <= 0) {
			throw new IllegalArgumentException("Alphabet size must be strictly positive.");
		}
		if (mInternalTransitionDensity < 0 || mInternalTransitionDensity > 1) {
			throw new IllegalArgumentException("Transition density must be between 0 and 1.");
		}
		if (mAcceptanceDensity < 0 || mAcceptanceDensity > 1) {
			throw new IllegalArgumentException("Acceptance density must be between 0 and 1.");
		}
	}

	private void addStates(final int numOfAccStates, final List<String> num2State, final String initialState,
			final NestedWordAutomaton<String, String> result) {
		final List<String> shuffledStateList = new ArrayList<>(num2State);
		Collections.shuffle(shuffledStateList, mRandom);
		// • Accepting states:
		for (int i = 0; i < numOfAccStates; ++i) {
			final String state = shuffledStateList.get(i);
			if (state.equals(initialState)) {
				result.addState(true, true, state);
			} else {
				result.addState(false, true, state);
			}
		}
		// • Non-accepting states:
		for (int i = numOfAccStates; i < mSize; ++i) {
			final String state = shuffledStateList.get(i);
			if (state.equals(initialState)) {
				result.addState(true, false, state);
			} else {
				result.addState(false, false, state);
			}
		}
	}

	@SuppressWarnings("squid:S00103")
	private void addInternalTransitions(final int maxNumOfTransitions, final int numOfTransitions,
			final List<String> num2State, final List<String> num2Letter,
			final NestedWordAutomaton<String, String> result) {
		/*
		 * What follows is essentially an implementation of the approach described in
		 * [1]. However, the transition function is not encoded as a bit-stream and the
		 * transitions are numbered slightly differently.
		 * 
		 * TRANSITION NUMBERS
		 * ──────────────────
		 * Let n = |Q| be the number of states and k = |Σ| the number of symbols. Then
		 * there are n²k possible transitions. Every transition gets assigned a unique
		 * number between 0 and n²k−1.
		 * The number assigned to the transition ⟨qₚ,aₓ⟩ ↦ qₛ is
		 *   p·(kn) + x·(n) + s .
		 * 
		 *   0 ···                                                             ··· n²k−1
		 * ┏━━━━┳╺╺╺╺┳━━━━┳━  ━┳━━━━┳╺╺╺╺┳━━━━┳━   ━┳━━━━┳╺╺╺╺┳━━━━┳━  ━┳━━━━┳╺╺╺╺┳━━━━┓
		 * ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ·· ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ··· ┃ q₀ ┃ ·· ┃qₙ₋₁┃ ·· ┃ q₀ ┃ ·· ┃qₙ₋₁┃
		 * ┗━━━━┻╸╸╸╸┻━━━━┻━  ━┻━━━━┻╸╸╸╸┻━━━━┻━   ━┻━━━━┻╸╸╸╸┻━━━━┻━  ━┻━━━━┻╸╸╸╸┻━━━━┛
		 * ╰───── a₀ ─────╯    ╰──── aₖ₋₁ ────╯     ╰───── a₀ ─────╯    ╰──── aₖ₋₁ ────╯
		 * │                                  │ ··· │                                  │
		 * ╰─────────────── q₀ ───────────────╯     ╰────────────── qₙ₋₁ ──────────────╯
		 * 
		 * [1] Marco Almeida, Nelma Moreira and Rogério Reis,
		 *     “On the Performance of Automata Minimization Algorithms” (2008),
		 *     Section 4 (“Random Automata Generation”).
		 */

		// --------------------------------------------------------------------
		// Add n−1 transitions s.t. every state becomes reachable from q₀.
		//
		final List<Integer> reachedStateNbs = new ArrayList<>(mSize);
		reachedStateNbs.add(0); // [q₀]

		// Q \{q₀} in random order:
		final List<Integer> shuffledStateNbList = new ArrayList<>(mSize - 1);
		for (int stateNb = 1; stateNb < mSize; ++stateNb) {
			shuffledStateNbList.add(stateNb);
		}
		Collections.shuffle(shuffledStateNbList, mRandom);

		// Transition numbers that will not be used again:
		final Set<Integer> usedTransitionNbs = new HashSet<>(mSize - 1);

		for (int i = 0; i < shuffledStateNbList.size(); ++i) {
			// random reached state
			final int predStateNb = reachedStateNbs.get(mRandom.nextInt(reachedStateNbs.size()));
			// random letter
			final int letterNb = mRandom.nextInt(mAlphabetSize);
			// rd. isolated state
			final int succStateNb = shuffledStateNbList.get(i);
			reachedStateNbs.add(succStateNb);
			final int transitionNb = predStateNb * mAlphabetSize * mSize + letterNb * mSize + succStateNb;
			usedTransitionNbs.add(transitionNb);
			final String predState = num2State.get(predStateNb);
			final String letter = num2Letter.get(letterNb);
			final String succState = num2State.get(succStateNb);
			result.addInternalTransition(predState, letter, succState);
		}

		// --------------------------------------------------------------------
		// Add further random transitions until the desired density is reached.
		//
		// Unused transition numbers in random order:
		final List<Integer> shuffledTransitionNbList = new ArrayList<>(maxNumOfTransitions - mSize + 1);
		for (int transNb = 0; transNb < maxNumOfTransitions; ++transNb) {
			if (!usedTransitionNbs.contains(transNb)) {
				shuffledTransitionNbList.add(transNb);
			}
		}
		Collections.shuffle(shuffledTransitionNbList, mRandom);

		final int remainingNumOfTransitions = numOfTransitions - mSize + 1;
		for (int i = 0; i < remainingNumOfTransitions; ++i) {
			final int transitionNb = shuffledTransitionNbList.get(i);
			final int predStateNb = transitionNb / (mAlphabetSize * mSize);
			final int letterNb = (transitionNb % (mAlphabetSize * mSize)) / mSize;
			final int succStateNb = transitionNb % mSize;
			final String predState = num2State.get(predStateNb);
			final String letter = num2Letter.get(letterNb);
			final String succState = num2State.get(succStateNb);
			result.addInternalTransition(predState, letter, succState);
		}
	}

	@SuppressWarnings("squid:S3047")
	private void addCallReturnTransitions(final List<String> num2State, final List<String> num2Letter,
			final NestedWordAutomaton<String, String> result) {
		for (final String pred : num2State) {
			for (final String letter : num2Letter) {
				for (final String succ : num2State) {
					tryToAddCallTransition(result, pred, letter, succ);
				}
			}
		}

		for (final String pred : num2State) {
			for (final String hier : num2State) {
				for (final String letter : num2Letter) {
					tryToAddReturnTransition(num2State, result, pred, hier, letter);
				}
			}
		}
	}

	private void tryToAddCallTransition(final NestedWordAutomaton<String, String> result, final String pred,
			final String letter, final String succ) {
		if (mRandom.nextFloat() < mCallTransitionDensity) {
			result.addCallTransition(pred, letter, succ);
		}
	}

	private void tryToAddReturnTransition(final List<String> num2State,
			final NestedWordAutomaton<String, String> result, final String pred, final String hier,
			final String letter) {
		for (final String succ : num2State) {
			if (mRandom.nextFloat() < mReturnTransitionDensity) {
				result.addReturnTransition(pred, hier, letter, succ);
			}
		}
	}
}
