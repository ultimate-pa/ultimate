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
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class BuchiIntersect<LETTER, STATE> implements IOperation<LETTER, STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER, STATE> mSndOperand;
	private BuchiIntersectNwa<LETTER, STATE> mIntersect;
	private NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private final IStateFactory<STATE> mStateFactory;
	
	public BuchiIntersect(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = mFstOperand.getStateFactory();
		doIntersect();
	}
	
	public BuchiIntersect(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER, STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER, STATE> sndOperand,
			final IStateFactory<STATE> sf) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = sf;
		doIntersect();
	}
	
	@Override
	public String operationName() {
		return "buchiIntersect";
	}
	
	@Override
	public String startMessage() {
		return "Start intersect. First operand " + mFstOperand.sizeInformation() + ". Second operand "
				+ mSndOperand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + mResult.sizeInformation();
	}
	
	private void doIntersect() throws AutomataLibraryException {
		mLogger.info(startMessage());
		mIntersect = new BuchiIntersectNwa<LETTER, STATE>(mFstOperand, mSndOperand, mStateFactory);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mIntersect);
		mLogger.info(exitMessage());
	}
	
	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> sf) throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		boolean correct = true;
//		final INestedWordAutomaton<LETTER, STATE> resultDD =
//				(new BuchiIntersectDD<LETTER, STATE>(mServices, mFstOperand, mSndOperand)).getResult();
//		correct &= (resultDD.size() <= mResult.size());
//		assert correct;
		correct &= resultCheckWithRandomWords();
		assert correct;
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
					operationName() + "Failed", "language is different",
					mFstOperand, mSndOperand);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	private boolean resultCheckWithRandomWords() throws AutomataLibraryException {
		final List<NestedLassoWord<LETTER>> lassoWords =
				new ArrayList<NestedLassoWord<LETTER>>();
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mResult);
		if (!resultEmptiness.getResult()) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> fstOperandEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mFstOperand);
		if (fstOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else {
			lassoWords.add(fstOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> sndOperandEmptiness =
				new BuchiIsEmpty<LETTER, STATE>(mServices, mSndOperand);
		if (sndOperandEmptiness.getResult()) {
			assert resultEmptiness.getResult();
		} else {
			lassoWords.add(sndOperandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mFstOperand.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mSndOperand.size()));
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, mFstOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, mSndOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, mResult)).getResult());
		boolean correct = true;
		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			correct &= checkAcceptance(nlw, mFstOperand, mSndOperand);
			assert correct;
		}
		return correct;
	}
	
	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INestedWordAutomatonSimple<LETTER, STATE> operand1,
			final INestedWordAutomatonSimple<LETTER, STATE> operand2)
					throws AutomataLibraryException {
		final boolean op1 = (new BuchiAccepts<LETTER, STATE>(mServices, operand1, nlw)).getResult();
		final boolean op2 = (new BuchiAccepts<LETTER, STATE>(mServices, operand2, nlw)).getResult();
		final boolean res = (new BuchiAccepts<LETTER, STATE>(mServices, mResult, nlw)).getResult();
		return ((op1 && op2) == res);
	}
}
