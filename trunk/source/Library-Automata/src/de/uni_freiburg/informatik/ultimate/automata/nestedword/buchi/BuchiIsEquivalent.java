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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsDeterministic;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Test for language equivalence of two Buchi nested word automata.
 * <p>
 * There are two options available:
 * <ol>
 * <li>a cheap and sufficient semi-test,</li>
 * <li>an expensive and complete test.</li>
 * </ol>
 * <p>
 * The semi-test is characterized as follows. If the test finds a counterexample, the languages differ. If the test does
 * not find a counterexample, the result is uncertain, in which case we assume the languages are equivalent.<br>
 * The semi-test works as follows. We extract words from one automaton and test them on the other automaton. If this
 * test succeeds, we generate random words and compare the behavior of the two automata. If this test succeeds, we give
 * up and assume that the languages are equivalent.
 * <p>
 * The complete test checks language inclusion in both directions, which is a very expensive operation for Buchi
 * automata.
 * <p>
 * This operation can be run in a dynamic mode. In that case we use the complete test if the automaton is small or
 * deterministic, guarded by a small timeout. Otherwise we use the incomplete test.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiIsEquivalent<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private static final int MAXIMUM_AUTOMATON_SIZE_FOR_DYNAMIC_TEST = 10;
	private static final int TIMEOUT_MILLISECONDS_FOR_DYNAMIC_TEST = 1_000;
	private static final int NUMBER_OF_ONE_SYMBOL_RANDOM_WORDS = 6;
	private static final int NUMBER_OF_TWO_SYMBOL_RANDOM_WORDS = 11;

	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final boolean mResult;
	private NestedLassoWord<LETTER> mCounterexample;
	private boolean mCompleteTestWasApplied;
	private String mMessage;

	/**
	 * Mode of the test.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	public enum TestMode {
		/**
		 * Complete test.
		 */
		COMPLETE,
		/**
		 * Complete test if the automata are small or deterministic. Fall-back to incomplete test in case of short
		 * timeout.
		 */
		DYNAMIC,
		/**
		 * Incomplete test.
		 */
		INCOMPLETE
	}

	/**
	 * Constructor which dynamically chooses which test to use in the interest of performance.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if some operation fails
	 */
	public BuchiIsEquivalent(final AutomataLibraryServices services,
			final IBuchiNwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand, TestMode.DYNAMIC);
	}

	/**
	 * General constructor with the option to perform an expensive but complete test.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory for (Buchi or finite-word) inclusion checks
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param mode
	 *            mode determining whether, e.g., a complete but expensive test should be applied
	 * @throws AutomataLibraryException
	 *             if some operation fails
	 */
	public BuchiIsEquivalent(final AutomataLibraryServices services,
			final IBuchiNwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand, final TestMode mode)
			throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;

		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(), "The operands have different alphabets.");
		}

		printStartMessage();
		mResult = run(stateFactory, mode);
		printExitMessage();
	}

	@Override
	public String exitMessage() {
		if (!mResult) {
			return "Buchi automata are not equivalent.";
		}
		if (mCompleteTestWasApplied) {
			return "Complete test succeeded. Buchi automata are equivalent.";
		}
		return "Incomplete test succeeded. Buchi automata could be equivalent.";
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	/**
	 * @return A counterexample (if available).
	 */
	public NestedLassoWord<LETTER> getCounterexample() {
		if (mResult) {
			throw new UnsupportedOperationException("No counterexample available.");
		}
		return mCounterexample;
	}

	/**
	 * @return A message describing the violation if available, {@code null} otherwise.
	 */
	public String getViolationMessage() {
		return mMessage;
	}

	/**
	 * @return {@code true} if the Buchi languages are equivalent and complete test was used. In case of a
	 *         counterexample the result is arbitrary.
	 */
	public boolean isCompleteTestUsed() {
		return mCompleteTestWasApplied;
	}

	private boolean run(final IBuchiNwaInclusionStateFactory<STATE> stateFactory, final TestMode mode)
			throws AutomataLibraryException {
		switch (mode) {
			case COMPLETE:
				return checkEquivalencePrecisely(mServices, stateFactory);
			case DYNAMIC:
				return checkEquivalenceDynamically(stateFactory);
			case INCOMPLETE:
				return checkEquivalenceImprecisely();
			default:
				throw new IllegalArgumentException("Unknown test mode: " + mode);
		}
	}

	private boolean checkEquivalencePrecisely(final AutomataLibraryServices services,
			final IBuchiNwaInclusionStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		// check inclusion of first operand language in second operand language
		if (!checkInclusionPrecisely(services, stateFactory, mFstOperand, mSndOperand)) {
			mMessage = "The first operand recognizes a word not recognized by the second one.";
			return false;
		}
		// check inclusion of second operand language in first operand language
		if (!checkInclusionPrecisely(services, stateFactory, mSndOperand, mFstOperand)) {
			mMessage = "The second operand recognizes a word not recognized by the first one.";
			return false;
		}
		mCompleteTestWasApplied = true;
		return true;
	}

	private boolean checkInclusionPrecisely(final AutomataLibraryServices services,
			final IBuchiNwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		final NestedLassoRun<LETTER, STATE> counterexample =
				(new BuchiIsIncluded<>(services, stateFactory, fstOperand, sndOperand)).getCounterexample();
		if (counterexample != null) {
			mCounterexample = counterexample.getNestedLassoWord();
			return false;
		}
		return true;
	}

	private boolean checkEquivalenceImprecisely() throws AutomataLibraryException {
		// extract some lasso words from the first automaton and check them on the second automaton
		if (!extractAndCheckLassoWords(mFstOperand, mSndOperand)) {
			mMessage = "The first operand recognizes a word not recognized by the second one.";
			return false;
		}

		// extract some lasso words from the second automaton and check them on the first automaton
		if (!extractAndCheckLassoWords(mSndOperand, mFstOperand)) {
			mMessage = "The second operand recognizes a word not recognized by the first one.";
			return false;
		}

		// generate some small random lasso words and compare acceptance of the two automata
		if (!generateAndCompareRandomLassoWords()) {
			mMessage = "One of the operands recognizes a word not recognized by the other one.";
			return false;
		}

		return true;
	}

	private boolean checkEquivalenceDynamically(final IBuchiNwaInclusionStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		boolean tryCompleteTest = mFstOperand.size() <= MAXIMUM_AUTOMATON_SIZE_FOR_DYNAMIC_TEST
				&& mSndOperand.size() <= MAXIMUM_AUTOMATON_SIZE_FOR_DYNAMIC_TEST;
		tryCompleteTest = tryCompleteTest || (new IsDeterministic<>(mServices, mFstOperand).getResult()
				&& new IsDeterministic<>(mServices, mSndOperand).getResult());
		if (tryCompleteTest) {
			try {
				return checkEquivalencePrecisely(
						new AutomataLibraryServices(mServices, TIMEOUT_MILLISECONDS_FOR_DYNAMIC_TEST), stateFactory);
			} catch (final AutomataOperationCanceledException e) {
				// fall back to incomplete test in case of timeout
			}
		}
		if (!mServices.getProgressAwareTimer().continueProcessing()) {
			throw new AutomataOperationCanceledException(getClass());
		}
		return checkEquivalenceImprecisely();
	}

	private boolean extractAndCheckLassoWords(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> source,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> target) throws AutomataLibraryException {
		// extract lasso words from the source automaton
		final List<NestedLassoWord<LETTER>> nestedLassoWords = new ArrayList<>();
		nestedLassoWords.addAll((new LassoExtractor<>(mServices, source)).getResult());

		// check on the target automaton
		return checkLassoWords(target, nestedLassoWords);
	}

	private boolean checkLassoWords(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final List<NestedLassoWord<LETTER>> nestedLassoWords) throws AutomataLibraryException {
		for (final NestedLassoWord<LETTER> nestedLassoWord : nestedLassoWords) {
			if (!checkLassoWord(automaton, nestedLassoWord)) {
				mCounterexample = nestedLassoWord;
				return false;
			}
		}
		return true;
	}

	private boolean checkLassoWord(final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> automaton,
			final NestedLassoWord<LETTER> nestedLassoWord) throws AutomataLibraryException {
		return (new BuchiAccepts<>(mServices, automaton, nestedLassoWord)).getResult();
	}

	/**
	 * @return Some small random lasso words.
	 * @throws AutomataLibraryException
	 *             if lasso word generation fails
	 */
	private boolean generateAndCompareRandomLassoWords() throws AutomataLibraryException {
		final List<NestedLassoWord<LETTER>> randomNestedLassoWords = new ArrayList<>();

		final int numberOfOneSymbolWords = NUMBER_OF_ONE_SYMBOL_RANDOM_WORDS;
		addRandomLassoWords(randomNestedLassoWords, 1, numberOfOneSymbolWords);

		final int numberOfTwoSymbolWords = NUMBER_OF_TWO_SYMBOL_RANDOM_WORDS;
		addRandomLassoWords(randomNestedLassoWords, 2, numberOfTwoSymbolWords);

		// compare the behavior on the random lasso words
		return compareOnLassoWords(randomNestedLassoWords);
	}

	private void addRandomLassoWords(final List<NestedLassoWord<LETTER>> nestedLassoWords, final int lengthOfWords,
			final int numberOfWords) {
		for (int i = 0; i < numberOfWords; ++i) {
			nestedLassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mFstOperand, lengthOfWords, i));
		}
	}

	private boolean compareOnLassoWords(final List<NestedLassoWord<LETTER>> nestedLassoWords)
			throws AutomataLibraryException {
		for (final NestedLassoWord<LETTER> nestedLassoWord : nestedLassoWords) {
			// acceptance check on random word for first automaton
			final boolean accepted1 = checkLassoWord(mFstOperand, nestedLassoWord);

			// acceptance check on random word for second automaton
			final boolean accepted2 = checkLassoWord(mSndOperand, nestedLassoWord);

			// check whether results are equal
			if (accepted1 != accepted2) {
				mCounterexample = nestedLassoWord;
				return false;
			}
		}
		return true;
	}
}
