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

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;


public class BuchiDifferenceFKV<LETTER,STATE> extends AbstractBuchiDifference<LETTER, STATE> {
	private BuchiComplementFKVNwa<LETTER,STATE> mSndComplemented;
	
	/**
	 * Creates a PowersetDeterminizer.
	 * 
	 * @param services Ultimate services
	 * @param stateFactory state factory used by PowersetDeterminizer
	 * @param fstOperand first operand
	 * @param sndOperand second operand
	 * @throws AutomataLibraryException if construction fails
	 */
	public BuchiDifferenceFKV(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER,STATE> sndOperand)
					throws AutomataLibraryException {
		/**
		 * TODO Christian 2016-08-12: Is it really intended to use the state
		 *      factory of the first operand instead of the one passed in the
		 *      constructor here?
		 */
		super(services, fstOperand.getStateFactory(), fstOperand, sndOperand);
		final IStateDeterminizer<LETTER, STATE> stateDeterminizer =
				new PowersetDeterminizer<LETTER,STATE>(sndOperand, true, stateFactory);
		mLogger.info(startMessage());
		constructResult(stateDeterminizer, Integer.MAX_VALUE, FkvOptimization.HeiMat2);
		mLogger.info(exitMessage());
	}
	
	/**
	 * Constructor with state determinizer.
	 * 
	 * @param services Ultimate services
	 * @param stateFactory state factory
	 * @param fstOperand first operand
	 * @param sndOperand second operand
	 * @param stateDeterminizer state determinizer
	 * @param optimization optimization parameter
	 * @param userDefinedMaxRank user defined max. rank
	 * @throws AutomataLibraryException if construction fails
	 */
	public BuchiDifferenceFKV(final AutomataLibraryServices services,
			final IStateFactory<STATE> stateFactory,
			final INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER,STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			final String optimization,
			final int userDefinedMaxRank)
					throws AutomataLibraryException {
		super(services, stateFactory, fstOperand, sndOperand);
		mLogger.info(startMessage());
		constructResult(stateDeterminizer, userDefinedMaxRank,
				FkvOptimization.valueOf(optimization));
		mLogger.info(exitMessage());
	}
	
	private void constructResult(
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			final int userDefinedMaxRank,
			final FkvOptimization optimization)
					throws AutomataLibraryException {
		mSndComplemented = new BuchiComplementFKVNwa<LETTER, STATE>(
				mServices, mSndOperand, stateDeterminizer, mStateFactory,
				optimization, userDefinedMaxRank);
		
		constructDifferenceFromComplement();
	}
	
	public int getHighestRank() {
		return mSndComplemented.getHighesRank();
	}
		
	@Override
	public String operationName() {
		return "buchiDifferenceFKV";
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + ". First operand "
				+ mFstOperand.sizeInformation() + ". Second operand "
				+ mSndOperand.sizeInformation() + " Result "
				+ mResult.sizeInformation()
				+ " Complement of second has " + mSndComplemented.size()
				+ " states "
				+ mSndComplemented.getPowersetStates() + " powerset states"
				+ mSndComplemented.getRankStates() + " rank states"
				+ " the highest rank that occured is "
				+ mSndComplemented.getHighesRank();
	}
	
	@Override
	public BuchiComplementFKVNwa<LETTER, STATE> getSndComplemented() {
		return mSndComplemented;
	}
}
