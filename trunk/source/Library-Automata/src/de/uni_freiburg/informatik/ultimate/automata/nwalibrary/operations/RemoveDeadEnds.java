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

import java.util.Collection;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.LibraryIdentifiers;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonOldApi;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomatonFilteredStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.TransitionConsitenceCheck;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.reachableStatesAutomaton.NestedWordAutomatonReachableStates;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.core.model.services.ILogger;

public class RemoveDeadEnds<LETTER,STATE> implements IOperation<LETTER,STATE> {
	
	private final AutomataLibraryServices mServices;
	private final INestedWordAutomatonSimple<LETTER,STATE> mInput;
	private final NestedWordAutomatonReachableStates<LETTER,STATE> mReach;
	private final INestedWordAutomatonOldApi<LETTER,STATE> mResult;

	private final ILogger mLogger;

	/**
	 * Given an INestedWordAutomaton nwa return a nested word automaton that has
	 * the same states, but all states that are not reachable or dead ends are
	 * omitted. (A dead end is a state from which no accepting state can be 
	 * reached).
	 * Each state of the result also occurred in the input. Only the auxiliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws AutomataOperationCanceledException
	 */
	public RemoveDeadEnds(AutomataLibraryServices services,
			INestedWordAutomatonSimple<LETTER,STATE> nwa)
			throws AutomataOperationCanceledException {
		mServices = services;
		mLogger = mServices.getLoggingService().getLogger(LibraryIdentifiers.PLUGIN_ID);
		mInput = nwa;
		mLogger.info(startMessage());
		try {
			mReach = new NestedWordAutomatonReachableStates<LETTER, STATE>(mServices, mInput);
			mReach.computeDeadEnds();
			mResult = new NestedWordAutomatonFilteredStates<LETTER, STATE>(mServices, mReach, mReach.getWithOutDeadEnds());
		} catch (final AutomataOperationCanceledException oce) {
			throw new AutomataOperationCanceledException(getClass());
		}
		mLogger.info(exitMessage());
		assert (new TransitionConsitenceCheck<LETTER, STATE>(mResult)).consistentForAll();
	}
	

	@Override
	public String operationName() {
		return "removeDeadEnds";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ mInput.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Reduced from " 
				+ mInput.sizeInformation() + " to "
				+ mResult.sizeInformation();
	}


	@Override
	public INestedWordAutomatonOldApi<LETTER, STATE> getResult() throws AutomataOperationCanceledException {
		return mResult;
	}
	
	@Override
	public boolean checkResult(StateFactory<STATE> stateFactory) throws AutomataOperationCanceledException {
		mLogger.info("Start testing correctness of " + operationName());
		boolean correct = true;
//		correct &= (ResultChecker.nwaLanguageInclusion(mInput, mResult) == null);
//		correct &= (ResultChecker.nwaLanguageInclusion(mResult, mInput) == null);
		assert correct;
		INestedWordAutomatonOldApi<LETTER, STATE> input;
		if (mInput instanceof INestedWordAutomatonOldApi) {
			input = (INestedWordAutomatonOldApi<LETTER, STATE>) mInput;
		} else {
			input = (new RemoveUnreachable<LETTER, STATE>(mServices, mInput)).getResult(); 
		}
		final ReachableStatesCopy<LETTER, STATE> rsc = 
				(new ReachableStatesCopy<LETTER, STATE>(mServices, input, false, false, false, false));
//		Set<UpDownEntry<STATE>> rsaEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : mReach.getRemovedUpDownEntry()) {
//			rsaEntries.add(rde);
//		}
//		Set<UpDownEntry<STATE>> rscEntries = new HashSet<UpDownEntry<STATE>>();
//		for (UpDownEntry<STATE> rde : rsc.getRemovedUpDownEntry()) {
//			rscEntries.add(rde);
//		}
//		correct &= ResultChecker.isSubset(rsaEntries,rscEntries);
//		assert correct;
//		correct &= ResultChecker.isSubset(rscEntries,rsaEntries);
//		assert correct;
		rsc.removeDeadEnds();
		final DoubleDeckerAutomaton<LETTER, STATE> reachalbeStatesCopy = (DoubleDeckerAutomaton<LETTER, STATE>) rsc.getResult();
		correct &= mResult.getStates().isEmpty() || ResultChecker.isSubset(reachalbeStatesCopy.getStates(),mResult.getStates());
		assert correct;
		correct &= ResultChecker.isSubset(mResult.getStates(),reachalbeStatesCopy.getStates());
		assert correct;
		final Collection<STATE> rsaStates = mResult.getStates();
		final Collection<STATE> rscStates = reachalbeStatesCopy.getStates();
		correct &= ResultChecker.isSubset(rsaStates,rscStates);
		assert correct;
		correct &= ResultChecker.isSubset(rscStates,rsaStates);
		assert correct;
		for (final STATE state : reachalbeStatesCopy.getStates()) {
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.internalSuccessors(state)) {
				correct &= mReach.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.callSuccessors(state)) {
				// TODO: fix or remove
				 correct &= mReach.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				// ignore call transitions
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : reachalbeStatesCopy.returnSuccessors(state)) {
				correct &= mReach.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingInternalTransition<LETTER, STATE> outTrans : mResult.internalSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsInternalTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingCallTransition<LETTER, STATE> outTrans : mResult.callSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsCallTransition(state, outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			for (final OutgoingReturnTransition<LETTER, STATE> outTrans : mResult.returnSuccessors(state)) {
				correct &= reachalbeStatesCopy.containsReturnTransition(state, outTrans.getHierPred(), outTrans.getLetter(), outTrans.getSucc());
				assert correct;
			}
			final Set<STATE> rCSdownStates = reachalbeStatesCopy.getDownStates(state);
			final Set<STATE> rCAdownStates = mReach.getWithOutDeadEnds().getDownStates(state);
			correct &= ResultChecker.isSubset(rCAdownStates, rCSdownStates);
			assert correct;
			// After enhanced non-live/dead end removal the following does not
			// hold.
//			 correct &= ResultChecker.isSubset(rCSdownStates, rCAdownStates);
			assert correct;
		}
		if (!correct) {
			ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mInput);
		}
		mLogger.info("Finished testing correctness of " + operationName());
		return correct;
	}


}
