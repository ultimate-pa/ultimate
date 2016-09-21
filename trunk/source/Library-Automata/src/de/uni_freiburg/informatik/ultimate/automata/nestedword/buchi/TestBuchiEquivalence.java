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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.GetRandomNestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Test for language equivalence of two Buchi automata or Buchi nested word automata.
 * <p>
 * There are two options available:
 * <ul>
 * <li>a cheap and sufficient semi-test,</li>
 * <li>an expensive and complete test.</li>
 * </ul>
 * <p>
 * The semi-test is characterized as follows.
 * If the test finds a counterexample, the languages differ.
 * If the test does not find a counterexample, the result is uncertain, in which case we assume the languages are
 * equivalent.<br>
 * The semi-test works as follows.
 * First the finite language is compared.
 * If this test fails, we extract words from one automaton and test them on the other automaton.
 * If this test succeeds, we generate random words and compare the behavior of the two automata.
 * If this test succeeds, we give up and assume that the languages are equivalent.
 * <p>
 * The complete test checks language inclusion in both directions, which is a very expensive operation for Buchi
 * automata.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class TestBuchiEquivalence<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE> {
	private final IStateFactory<STATE> mStateFactory;
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private final boolean mResult;
	
	/**
	 * Constructor which performs a sufficient but cheaper equivalence test.
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
	public TestBuchiEquivalence(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand, false);
	}
	
	/**
	 * General constructor with the option to perform an expensive but complete test.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param completeTest
	 *            true iff a complete but expensive test should be applied
	 * @throws AutomataLibraryException
	 *             if some operation fails
	 */
	public TestBuchiEquivalence(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand,
			final boolean completeTest) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = stateFactory;
		
		if (!INestedWordAutomatonSimple.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(), "The operands have different alphabets.");
		}
		
		mLogger.info(startMessage());
		if (completeTest) {
			mResult = checkEquivalencePrecisely();
		} else {
			mResult = checkEquivalence();
		}
		mLogger.info(exitMessage());
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}
	
	@Override
	public Boolean getResult() {
		return mResult;
	}
	
	private boolean checkEquivalencePrecisely() throws AutomataLibraryException {
		boolean correct = true;
		
		NestedLassoRun<LETTER, STATE> counterexample;
		
		// check inclusion of first operand language in second operand language
		counterexample = (new BuchiIsIncluded<>(mServices, mStateFactory, mFstOperand, mSndOperand))
				.getCounterexample();
		correct &= (counterexample == null);
		
		// check inclusion of second operand language in first operand language
		counterexample = (new BuchiIsIncluded<>(mServices, mStateFactory, mSndOperand, mFstOperand))
				.getCounterexample();
		correct &= (counterexample == null);
		
		return correct;
	}
	
	private boolean checkEquivalence() throws AutomataLibraryException {
		boolean correct = true;
		
		// We first do a semi-test for finite language equivalence, which is a sufficient criterion.
		correct &= (new IsIncluded<>(mServices, mStateFactory, mFstOperand, mSndOperand)).getResult();
		correct &= (new IsIncluded<>(mServices, mStateFactory, mSndOperand, mFstOperand)).getResult();
		
		if (!correct) {
			// The finite language is not equivalent. Check with some lasso words.
			correct = true;
			
			// extract some words from the first automaton and check them on the second automaton
			correct &= extractAndCheckLassoWords(mFstOperand, mSndOperand);
			
			// extract some words from the second automaton and check them on the first automaton
			correct &= extractAndCheckLassoWords(mSndOperand, mFstOperand);
			
			// generate some small random lasso words and compare acceptance of the two automata
			correct &= generateAndCompareRandomLassoWords();
		}
		
		return correct;
	}
	
	private boolean extractAndCheckLassoWords(final INestedWordAutomatonSimple<LETTER, STATE> source,
			final INestedWordAutomatonSimple<LETTER, STATE> target) throws AutomataLibraryException {
		
		// extract lasso words from the source automaton
		final List<NestedLassoWord<LETTER>> nestedLassoWords = new ArrayList<>();
		nestedLassoWords.addAll((new LassoExtractor<>(mServices, source)).getResult());
		
		// check on the target automaton
		return checkLassoWords(target, nestedLassoWords);
	}
	
	private boolean checkLassoWords(final INestedWordAutomatonSimple<LETTER, STATE> automaton,
			final List<NestedLassoWord<LETTER>> nestedLassoWords) throws AutomataLibraryException {
		for (final NestedLassoWord<LETTER> nestedLassoWord : nestedLassoWords) {
			if (!checkLassoWord(automaton, nestedLassoWord)) {
				return false;
			}
		}
		return true;
	}
	
	private boolean checkLassoWord(final INestedWordAutomatonSimple<LETTER, STATE> automaton,
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
		
		final int numberOfOneSymbolWords = 6;
		addRandomLassoWords(randomNestedLassoWords, 1, numberOfOneSymbolWords);
		
		final int numberOfTwoSymbolWords = 11;
		addRandomLassoWords(randomNestedLassoWords, 2, numberOfTwoSymbolWords);
		
		// compare the behavior on the random lasso words
		return compareOnLassoWords(randomNestedLassoWords);
	}
	
	private void addRandomLassoWords(final List<NestedLassoWord<LETTER>> nestedLassoWords, final int lengthOfWords,
			final int numberOfWords) {
		for (int i = 0; i < numberOfWords; ++i) {
			final NestedWord<LETTER> stem = (new GetRandomNestedWord<>(mFstOperand, lengthOfWords)).getResult();
			final NestedWord<LETTER> loop = (new GetRandomNestedWord<>(mFstOperand, lengthOfWords)).getResult();
			nestedLassoWords.add(new NestedLassoWord<>(stem, loop));
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
				return false;
			}
		}
		return true;
	}
}
