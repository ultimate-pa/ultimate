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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations;

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.DifferenceDD;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.IOpWithDelayedDeadEndRemoval;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;


public class Difference<LETTER,STATE> implements IOperation<LETTER,STATE>, IOpWithDelayedDeadEndRemoval<LETTER, STATE> {

	private final AutomataLibraryServices mServices;
	private final ILogger mLogger;
	
	private final INestedWordAutomatonSimple<LETTER,STATE> mFstOperand;
	private final INestedWordAutomatonSimple<LETTER,STATE> mSndOperand;
	private DeterminizeNwa<LETTER,STATE> mSndDeterminized;
	private final IStateDeterminizer<LETTER, STATE> mStateDeterminizer;
	private ComplementDeterministicNwa<LETTER,STATE> mSndComplemented;
	private IntersectNwa<LETTER, STATE> mIntersect;
	private NestedWordAutomatonReachableStates<LETTER,STATE> mResult;
	private NestedWordAutomatonFilteredStates<LETTER, STATE> mResultWOdeadEnds;
	private final StateFactory<STATE> mStateFactory;
	
	
	@Override
	public String operationName() {
		return "difference";
	}
	
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + ". First operand " + 
				mFstOperand.sizeInformation() + ". Second operand " + 
				mSndOperand.sizeInformation();	
	}
	
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + 
				mResult.sizeInformation();
	}
	
	
	
	
	public Difference(final AutomataLibraryServices services,
			final StateFactory<STATE> stateFactory, 
			final INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER,STATE> sndOperand
			) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = mFstOperand.getStateFactory();
		mStateDeterminizer = new PowersetDeterminizer<LETTER,STATE>(sndOperand, true, stateFactory);
		mLogger.info(startMessage());
		computateDifference(false);
		mLogger.info(exitMessage());
	}
	
	
	public Difference(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> fstOperand,
			final INestedWordAutomatonSimple<LETTER,STATE> sndOperand,
			final IStateDeterminizer<LETTER, STATE> stateDeterminizer,
			final StateFactory<STATE> sf,
			final boolean finalIsTrap) throws AutomataLibraryException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mFstOperand = fstOperand;
		mSndOperand = sndOperand;
		mStateFactory = sf;
		mStateDeterminizer = stateDeterminizer;
		mLogger.info(startMessage());
		try {
			computateDifference(finalIsTrap);
		} catch (final AutomataOperationCanceledException oce) {
			throw new AutomataOperationCanceledException(getClass());
		}
		mLogger.info(exitMessage());
	}
	
	private void computateDifference(final boolean finalIsTrap) throws AutomataLibraryException {
		if (mStateDeterminizer instanceof PowersetDeterminizer) {
			final TotalizeNwa<LETTER, STATE> sndTotalized = new TotalizeNwa<LETTER, STATE>(mSndOperand, mStateFactory);
			final ComplementDeterministicNwa<LETTER,STATE> sndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(sndTotalized);
			final IntersectNwa<LETTER, STATE> intersect = new IntersectNwa<LETTER, STATE>(mFstOperand, sndComplemented, mStateFactory, finalIsTrap);
			final NestedWordAutomatonReachableStates<LETTER, STATE> result = 
					new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, intersect);
			if (!sndTotalized.nonDeterminismInInputDetected()) {
				mSndComplemented = sndComplemented;
				mIntersect = intersect;
				mResult = result;
				mLogger.info("Subtrahend was deterministic. Have not used determinization.");
				return;
			} else {
			mLogger.info("Subtrahend was not deterministic. Recomputing result with determinization.");
			}
		}
		mSndDeterminized = new DeterminizeNwa<LETTER,STATE>(mServices, mSndOperand,mStateDeterminizer,mStateFactory, null, true);
		mSndComplemented = new ComplementDeterministicNwa<LETTER, STATE>(mSndDeterminized);
		mIntersect = new IntersectNwa<LETTER, STATE>(mFstOperand, mSndComplemented, mStateFactory, finalIsTrap);
		mResult = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mIntersect);
	}
	






	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult()
			throws AutomataOperationCanceledException {
		if (mResultWOdeadEnds == null) {
			return mResult;
		} else {
			return mResultWOdeadEnds;
		}
	}


	
	@Override
	public boolean checkResult(final StateFactory<STATE> sf) throws AutomataLibraryException {
		mLogger.info("Start testing correctness of " + operationName());
		final INestedWordAutomatonOldApi<LETTER, STATE> fstOperandOldApi = ResultChecker.getOldApiNwa(mServices, mFstOperand);
		final INestedWordAutomatonOldApi<LETTER, STATE> sndOperandOldApi = ResultChecker.getOldApiNwa(mServices, mSndOperand);
		final INestedWordAutomaton<LETTER, STATE> resultDD = 
				(new DifferenceDD<LETTER, STATE>(mServices, fstOperandOldApi,sndOperandOldApi, 
						new PowersetDeterminizer<LETTER, STATE>(sndOperandOldApi,true, sf),sf,false,false)).getResult();
		boolean correct = true;
//		correct &= (resultDD.size() == mResult.size());
//		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusionNew(mServices, resultDD, mResult, sf) == null);
		assert correct;
		correct &= (ResultChecker.nwaLanguageInclusionNew(mServices, mResult, resultDD, sf) == null);
		assert correct;
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mFstOperand,mSndOperand);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}





	@Override
	public boolean removeDeadEnds() throws AutomataOperationCanceledException {
		mResult.computeDeadEnds();
		mResultWOdeadEnds = new NestedWordAutomatonFilteredStates<LETTER, STATE>(mServices, mResult, mResult.getWithOutDeadEnds());
		mLogger.info("With dead ends: " + mResult.getStates().size());
		mLogger.info("Without dead ends: " + mResultWOdeadEnds.getStates().size());
		return mResult.getStates().size() != mResultWOdeadEnds.getStates().size();
	}


	@Override
	public long getDeadEndRemovalTime() {
		// TODO Auto-generated method stub
		return 0;
	}


	@Override
	public Iterable<UpDownEntry<STATE>> getRemovedUpDownEntry() {
		return mResult.getWithOutDeadEnds().getRemovedUpDownEntry();
	}


	public Map<STATE, Map<STATE, IntersectNwa<LETTER, STATE>.ProductState>> getFst2snd2res() {
		return mIntersect.getFst2snd2res();
	}
	
	
	
	
	
	
}

