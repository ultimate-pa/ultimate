/*
 * Copyright (C) 2011-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa;

import java.util.ArrayList;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.buchiNwa.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

	

/**
 * Buchi Complementation based on 
 * 2004ATVA - Friedgut,Kupferman,Vardi - Büchi Complementation Made Tighter
 * @author heizmann@informatik.uni-freiburg.de
 *
 */
public class BuchiComplementFKV<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	/**
	 * TODO Allow definition of a maximal rank for cases where you know that
	 * this is sound. E.g. if the automaton is reverse deterministic a maximal
	 * rank of 2 is suffient, see paper of Seth Forgaty.
	 */
	private final int mUserDefinedMaxRank;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> mOperand;
	private final NestedWordAutomatonReachableStates<LETTER, STATE> mResult;
	private final StateFactory<STATE> mStateFactory;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private final BuchiComplementFKVNwa<LETTER, STATE> mComplemented;
	private final FkvOptimization mOptimization;	
	
	
	
	@Override
	public String operationName() {
		return "buchiComplementFKV";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " with optimization " + mOptimization 
				+ ". Operand " +	mOperand.sizeInformation();
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " with optimization " + mOptimization 
				+ ". Operand " + 
				mOperand.sizeInformation() + " Result " + 
				mResult.sizeInformation() + 
				mComplemented.getPowersetStates() + " powerset states" +
				mComplemented.getRankStates() + " rank states" +
			" the highest rank that occured is " + mComplemented.getHighesRank();
	}
	
	public int getHighestRank() {
		return mComplemented.getHighesRank();
	}

	public BuchiComplementFKV(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory, 
			final INestedWordAutomatonSimple<LETTER,STATE> input,
			final String optimization,
			final int userDefinedMaxRank) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.mStateDeterminizer = new PowersetDeterminizer<LETTER, STATE>(input, true, stateFactory);
		this.mStateFactory = input.getStateFactory();
		this.mOperand = input;
		this.mUserDefinedMaxRank = userDefinedMaxRank;
		this.mOptimization = FkvOptimization.valueOf(optimization);
		mLogger.info(startMessage());
		mComplemented = new BuchiComplementFKVNwa<LETTER, STATE>(mServices, input,mStateDeterminizer,mStateFactory, mOptimization, mUserDefinedMaxRank);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mComplemented);
		mLogger.info(exitMessage());
	}
	
	public BuchiComplementFKV(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory, 
			final INestedWordAutomatonSimple<LETTER,STATE> input) throws AutomataLibraryException {
		this(services, stateFactory, input, FkvOptimization.HeiMat2.toString(), Integer.MAX_VALUE);
		
	}
	
	public BuchiComplementFKV(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> input, final IStateDeterminizer<LETTER, STATE> stateDeterminizier) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		this.mStateDeterminizer = stateDeterminizier;
		this.mStateFactory = input.getStateFactory();
		this.mOperand = input;
		this.mUserDefinedMaxRank = Integer.MAX_VALUE;
		this.mOptimization = FkvOptimization.HeiMat2;
		mLogger.info(startMessage());
		mComplemented = new BuchiComplementFKVNwa<LETTER, STATE>(mServices, input,mStateDeterminizer,mStateFactory, mOptimization, mUserDefinedMaxRank);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mComplemented);
		mLogger.info(exitMessage());
	}
	
	
	
	


	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		final boolean underApproximationOfComplement = false;
		boolean correct = true;
		mLogger.info("Start testing correctness of " + operationName());
		final INestedWordAutomaton<LETTER, STATE> operandOldApi = 
				ResultChecker.getNormalNwa(mServices, mOperand);
		final List<NestedLassoWord<LETTER>> lassoWords = new ArrayList<NestedLassoWord<LETTER>>();
		final BuchiIsEmpty<LETTER, STATE> operandEmptiness = new BuchiIsEmpty<LETTER, STATE>(mServices, operandOldApi);
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
		lassoWords.addAll((new LassoExtractor<LETTER, STATE>(mServices, operandOldApi)).getResult());
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
			boolean thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			if (!thistime) {
				thistime = checkAcceptance(nlw, operandOldApi, underApproximationOfComplement);
			}
			correct &= thistime;
//			assert correct;
		}

		if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mOperand);
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "FailedRes", "", mResult);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}
	
	
	private boolean checkAcceptance(final NestedLassoWord<LETTER> nlw,
			final INestedWordAutomaton<LETTER, STATE> operand , 
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
	public NestedWordAutomatonReachableStates<LETTER, STATE> getResult() throws AutomataLibraryException {
		return mResult;
	}

}
