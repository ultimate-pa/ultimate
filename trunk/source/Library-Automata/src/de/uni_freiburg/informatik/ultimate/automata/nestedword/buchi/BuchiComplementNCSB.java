/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.UnaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.reachablestates.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Buchi Complementation based on the algorithm proposed by Frantisek Blahoudek
 * and Jan Stejcek. This complementation is only sound for a special class of
 * automata whose working title is TABA (termination analysis Büchi automata).
 * 
 * @author heizmann@informatik.uni-freiburg.de
 * @param <LETTER> letter type
 * @param <STATE> state type
 */
public class BuchiComplementNCSB<LETTER, STATE> extends UnaryNwaOperation<LETTER, STATE> {
	
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	
	public BuchiComplementNCSB(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER, STATE> input) throws AutomataLibraryException {
		super(services);
		this.mOperand = input;
		mLogger.info(startMessage());
		final BuchiComplementNCSBNwa<LETTER, STATE> complemented =
				new BuchiComplementNCSBNwa<LETTER, STATE>(mServices, input, stateFactory);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(
				mServices, complemented);
		mLogger.info(exitMessage());
	}
	
	@Override
	public String operationName() {
		return "buchiComplementBS";
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Operand " + mOperand.sizeInformation() + " Result "
				+ mResult.sizeInformation();
	}
	
	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		final boolean underApproximationOfComplement = false;
		boolean correct = true;
		mLogger.info("Start testing correctness of " + operationName());
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<LETTER, STATE>(mServices, mOperand);
		final boolean operandEmpty = operandEmptiness.getResult();
		if (!operandEmpty) {
			lassoWords.add(operandEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		final BuchiIsEmpty<LETTER, STATE> resultEmptiness = new BuchiIsEmpty<LETTER, STATE>(mServices, mResult);
		final boolean resultEmpty = resultEmptiness.getResult();
		if (!resultEmpty) {
			lassoWords.add(resultEmptiness.getAcceptingNestedLassoRun().getNestedLassoWord());
		}
		correct &= !(operandEmpty && resultEmpty);
		assert correct;
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, mResult.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
//		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, operandOldApi.size()));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 1));
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, mOperand)).getResult());
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, mResult)).getResult());
		
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		lassoWords.add(ResultChecker.getRandomNestedLassoWord(mResult, 2));
		
		for (final NestedLassoWord<LETTER> nlw : lassoWords) {
			boolean thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, mOperand, underApproximationOfComplement);
			}
			correct &= thistime;
//			assert correct;
		}
		
		if (!correct) {
			AutomatonDefinitionPrinter.writeToFileIfPreferred(mServices,
					operationName() + "Failed", "language is different",
					mOperand, mResult);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INestedWordAutomatonSimple<LETTER, STATE> operand,
			final boolean underApproximationOfComplement) throws AutomataLibraryException {
		final boolean op = (new BuchiAccepts<LETTER, STATE>(mServices, operand, nlw)).getResult();
		final boolean res = (new BuchiAccepts<LETTER, STATE>(mServices, mResult, nlw)).getResult();
		boolean correct;
		if (underApproximationOfComplement) {
			correct = !res || op;
		} else {
			correct = op ^ res;
		}
//		assert correct : operationName() + " wrong result!";
		return correct;
	}
	
	@Override
	protected INestedWordAutomatonSimple<LETTER, STATE> getOperand() {
		return mOperand;
	}
	
	@Override
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() {
		return mResult;
	}
	
}
