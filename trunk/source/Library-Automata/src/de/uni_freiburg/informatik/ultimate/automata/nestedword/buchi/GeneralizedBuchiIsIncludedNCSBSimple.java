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
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationStatistics;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.BinaryNwaOperation;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IGeneralizedNwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.optncsb.Options;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiComplementNcsbStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IBuchiIntersectStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Operation that checks if the language of the first Buchi automaton is included in the language of the second Buchi
 * automaton.
 * Uses the NCSB algorithm for complementation of semideterministic Büchi
 * automata. Is unsound if rhs operand is not semideterministic.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 *         Yong Li (liyong@ios.ac.cn)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public final class GeneralizedBuchiIsIncludedNCSBSimple<LETTER, STATE> extends BinaryNwaOperation<LETTER, STATE, IStateFactory<STATE>> {


	private final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mFstOperand;
	private final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> mSndOperand;

	private final Boolean mResult;

	private final NestedLassoRun<LETTER, STATE> mCounterexample;

	/**
	 * Constructor.
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
	public <FACTORY extends IBuchiIntersectStateFactory<STATE> & IBuchiComplementNcsbStateFactory<STATE>> GeneralizedBuchiIsIncludedNCSBSimple(final AutomataLibraryServices services,
			final FACTORY stateFactory,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> fstOperand,
			final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndOperand) throws AutomataLibraryException {
		super(services);

		if(fstOperand instanceof IGeneralizedNwaOutgoingLetterAndTransitionProvider) {
			mFstOperand = (IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE>)fstOperand;
		}else {
			mFstOperand = new BuchiToGeneralizedBuchi<>(fstOperand);
		}
		
		mSndOperand = sndOperand;

		if (mLogger.isInfoEnabled()) {
			mLogger.info(startMessage());
		}

		final INwaOutgoingLetterAndTransitionProvider<LETTER, STATE> sndComplement =
				(new BuchiComplementNCSBSimple<LETTER, STATE>(mServices, stateFactory, mSndOperand)).getResult();
		final IGeneralizedNwaOutgoingLetterAndTransitionProvider<LETTER, STATE> difference =
				new GeneralizedBuchiIntersectNwa<>(mFstOperand, sndComplement, stateFactory);
		final GeneralizedBuchiIsEmpty<LETTER, STATE> emptinessCheck = new GeneralizedBuchiIsEmpty<>(mServices, difference);

		mResult = emptinessCheck.getResult();
		mCounterexample = emptinessCheck.getAcceptingNestedLassoRun();
		if(mCounterexample != null) {
			GeneralizedBuchiAccepts<LETTER, STATE> accepts = new GeneralizedBuchiAccepts<>(mServices, difference, mCounterexample.getNestedLassoWord());
			if(! accepts.getResult() ) {
				System.out.println("Not OK for difference accepts");
			}else {
				System.out.println("OK for difference accepts");
			}
			accepts = new GeneralizedBuchiAccepts<>(mServices, mFstOperand, mCounterexample.getNestedLassoWord());
			BuchiAccepts<LETTER, STATE> acc = new BuchiAccepts<>(mServices, fstOperand, mCounterexample.getNestedLassoWord());
			assert accepts.getResult().booleanValue() == acc.getResult().booleanValue();
			if(! accepts.getResult() ) {
				System.out.println("Not OK for mFstOperand accepts");
			}else {
				System.out.println("OK for mFstOperand accepts");
			}
			accepts = new GeneralizedBuchiAccepts<>(mServices, new BuchiToGeneralizedBuchi<>(sndComplement), mCounterexample.getNestedLassoWord());
			acc = new BuchiAccepts<>(mServices, sndComplement, mCounterexample.getNestedLassoWord());
			assert accepts.getResult().booleanValue() == acc.getResult().booleanValue();
			
			if(! accepts.getResult() ) {
				System.out.println("Not OK for sndComplement accepts");
				System.out.println(sndComplement);
				System.out.println(mCounterexample);
				System.out.println(mCounterexample.getNestedLassoWord());
				System.exit(1);
			}else {
				System.out.println("OK for sndComplement accepts");
			}
			
		}
		
		if(mCounterexample != null) {
			System.out.println(mCounterexample.getStem().getLength() + "," + mCounterexample.getLoop().getLength());
		}
		
		if (mLogger.isInfoEnabled()) {
			mLogger.info(exitMessage());
		}
	}

	@Override
	public String exitMessage() {
		return "Finished " + getOperationName() + ". Language is " + (mResult ? "" : "not ") + "included";
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

	public NestedLassoRun<LETTER, STATE> getCounterexample() {
		return mCounterexample;
	}

	@Override
	public boolean checkResult(final IStateFactory<STATE> stateFactory) throws AutomataLibraryException {
		return true;
	}
	
	@Override
	public AutomataOperationStatistics getAutomataOperationStatistics() {
		final AutomataOperationStatistics result = BuchiIsIncluded.constructBasicInclusionStatistics(mServices, mLogger, this);

		return result;
	}
	
	

}
