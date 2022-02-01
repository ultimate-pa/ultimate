/*
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomatonDefinitionPrinter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi intersection.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiIntersect<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;
	private NestedWordAutomatonReachableStates<LETTER, STATE> mResult;

	/**
	 * Full constructor.
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
	 *             if construction fails
	 */
	public <FACTORY extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> BuchiIntersect(
			final AutomataLibraryServices services, final FACTORY stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		doIntersect(stateFactory);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + " Result " + mResult.sizeInformation();
	}

	private <SF extends IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> void
			doIntersect(final SF stateFactory) throws AutomataLibraryException {
		final BuchiIntersectNwa<LETTER, STATE> intersect =
				new BuchiIntersectNwa<>(mFstOperand, mSndOperand, stateFactory);
		mResult = new NestedWordAutomatonReachableStates<>(mServices, intersect);
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
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() {
		return mResult;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Start testing correctness of " + getOperationName());
		}
		boolean correct = true;
		/*
		final INestedWordAutomaton<LETTER, STATE> resultDD =
				(new BuchiIntersectDD<LETTER, STATE>(mServices, mFstOperand, mSndOperand)).getResult();
		correct &= (resultDD.size() <= mResult.size());
		assert correct;
		*/
		correct &= resultCheckWithRandomWords();
		assert correct;
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices, getOperationName() + "Failed",
					"language is different", mFstOperand, mSndOperand);
		}
		if (mLogger.isInfoEnabled()) {
			mLogger.info("Finished testing correctness of " + getOperationName());
		}
		return correct;
	}

	private boolean resultCheckWithRandomWords() throws AutomataLibraryException {
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<>();
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<>(mServices, mResult);
		if (!resultEmptiness.getResult()) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> fstOperandEmptiness = new BuchiIsEmpty<>(mServices, mFstOperand);
		if (fstOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else {
			lassoWords.add(fstOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> sndOperandEmptiness = new BuchiIsEmpty<>(mServices, mSndOperand);
		if (sndOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else {
			lassoWords.add(sndOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mResult.size(), 0));
		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mFstOperand.size(), 1));
		lassoWords.add(NestedWordAutomataUtils.getRandomNestedLassoWord(mResult, mSndOperand.size(), 2));
		lassoWords.addAll((new LassoExtractor<>(mServices, mFstOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<>(mServices, mSndOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<>(mServices, mResult)).getResult());
		boolean correct = true;
		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			correct &= checkAcceptance(nlw, mFstOperand, mSndOperand);
			assert correct;
		}
		return correct;
	}

	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand1,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> operand2) throws AutomataLibraryException {
		final boolean op1 = (new BuchiAccepts<>(mServices, operand1, nlw)).getResult();
		final boolean op2 = (new BuchiAccepts<>(mServices, operand2, nlw)).getResult();
		final boolean res = (new BuchiAccepts<>(mServices, mResult, nlw)).getResult();
		return (op1 && op2) == res;
	}
}
