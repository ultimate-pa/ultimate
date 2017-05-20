/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaInclusionStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWord;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Test for language equivalence of two nested word automata.
 * <p>
 * The test checks language inclusion in both directions.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class IsEquivalent<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private final boolean mResult;
	private NestedWord<LETTER> mCounterexample;
	private String mMessage;

	/**
	 * @param services
	 *            Ultimate services.
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if some operation fails
	 */
	public IsEquivalent(final AutomataLibraryServices services, final INwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;

		if (!NestedWordAutomataUtils.sameAlphabet(mFstOperand, mSndOperand)) {
			throw new AutomataLibraryException(this.getClass(), "The operands have different alphabets.");
		}

		printStartMessage();
		mResult = checkEquivalence(stateFactory);
		printExitMessage();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getFirstOperand() {
		return mFstOperand;
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSecondOperand() {
		return mSndOperand;
	}

	@Override
	public Boolean getResult() {
		return mResult;
	}

	/**
	 * @return A counterexample (if available).
	 */
	public NestedWord<LETTER> getCounterexample() {
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

	private boolean checkEquivalence(final INwaInclusionStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		if (!checkInclusion(stateFactory, mFstOperand, mSndOperand)) {
			mMessage = "The first operand recognizes a word not recognized by the second one.";
			return false;
		}
		if (!checkInclusion(stateFactory, mSndOperand, mFstOperand)) {
			mMessage = "The second operand recognizes a word not recognized by the first one.";
			return false;
		}
		return true;
	}

	private boolean checkInclusion(final INwaInclusionStateFactory<STATE> stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		final IsIncluded<LETTER, STATE> isIncluded = new IsIncluded<>(mServices, stateFactory, fstOperand, sndOperand);
		if (!isIncluded.getResult()) {
			mCounterexample = isIncluded.getCounterexample().getWord();
			return false;
		}
		return true;
	}
}
