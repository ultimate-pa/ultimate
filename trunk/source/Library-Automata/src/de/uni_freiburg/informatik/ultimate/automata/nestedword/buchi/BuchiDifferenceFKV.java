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
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NwaOutgoingLetterAndTransitionAdapter;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi.MultiOptimizationLevelRankingGenerator.FkvOptimization;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IStateDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.PowersetDeterminizer;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementFkvStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IDeterminizeStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

/**
 * Buchi difference "<tt>FKV</tt>".
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class BuchiDifferenceFKV<LETTER, STATE> extends AbstractBuchiDifference<LETTER, STATE> {
	private BuchiComplementFKVNwa<LETTER, STATE> mOnDemandComplemented;
	private INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndComplemented;

	/**
	 * Constructor which creates a PowersetDeterminizer.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory used by PowersetDeterminizer
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public <SF extends IDeterminizeStateFactory<STATE> & IBuchiComplementFkvStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> BuchiDifferenceFKV(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		this(services, stateFactory, fstOperand, sndOperand, new PowersetDeterminizer<>(sndOperand, true, stateFactory),
				FkvOptimization.HEIMAT2, Integer.MAX_VALUE);
	}

	/**
	 * Full constructor with state determinizer.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param fstOperand
	 *            first operand
	 * @param sndOperand
	 *            second operand
	 * @param stateDeterminizer
	 *            state determinizer
	 * @param optimization
	 *            optimization parameter
	 * @param userDefinedMaxRank
	 *            user defined max. rank
	 * @throws AutomataLibraryException
	 *             if construction fails
	 */
	public <SF extends IBuchiComplementFkvStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>> BuchiDifferenceFKV(
			final AutomataLibraryServices services, final SF stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer, final FkvOptimization optimization,
			final int userDefinedMaxRank) throws AutomataLibraryException {
		super(services, fstOperand, sndOperand);

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}
		constructResult(stateFactory, stateDeterminizer, userDefinedMaxRank, optimization);
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	private <SF extends IBuchiComplementFkvStateFactory<STATE> & IBuchiIntersectStateFactory<STATE> & IEmptyStackStateFactory<STATE>>
			void constructResult(final SF stateFactory, final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
					final int userDefinedMaxRank, final FkvOptimization optimization) throws AutomataLibraryException {
		mOnDemandComplemented = new BuchiComplementFKVNwa<>(mServices, mSndOperand, stateDeterminizer, stateFactory,
				optimization, userDefinedMaxRank);
		mSndComplemented = new NwaOutgoingLetterAndTransitionAdapter<LETTER, STATE>(mOnDemandComplemented);
		constructDifferenceFromComplement(stateFactory);
	}

	public int getHighestRank() {
		return mOnDemandComplemented.getHighesRank();
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". First operand " + mFstOperand.sizeInformation() + " Second operand "
				+ mSndOperand.sizeInformation() + " Result " + mResult.sizeInformation() + " Complement of second has "
				+ mSndComplemented.size() + " states " + mOnDemandComplemented.getPowersetStates() + " powerset states"
				+ mOnDemandComplemented.getRankStates() + " rank states. The highest rank that occured is "
				+ mOnDemandComplemented.getHighesRank();
	}

	@Override
	public INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> getSndComplemented() {
		return mSndComplemented;
	}
}
