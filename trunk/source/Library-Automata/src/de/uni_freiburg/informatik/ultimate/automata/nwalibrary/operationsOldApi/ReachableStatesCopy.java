/*
 * Copyright (C) 2012-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operationsOldApi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsEmpty;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.IsIncluded;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nwalibrary.transitions.OutgoingReturnTransition;

public class ReachableStatesCopy<LETTER,STATE> extends DoubleDeckerBuilder<LETTER, STATE>
		implements IOperation<LETTER,STATE> {
	
	private final Map<STATE,STATE> mold2new = new HashMap<STATE,STATE>();
	private final Map<STATE,STATE> mnew2old = new HashMap<STATE,STATE>();

	private final INestedWordAutomatonSimple<LETTER,STATE> mInput;
	private final boolean mComplement;

	/**
	 * Given an INestedWordAutomaton nwa return a NestedWordAutomaton that has
	 * the same states, but all states that are not reachable are omitted.
	 * Each state of the result also occurred in the input. Only the auxilliary
	 * empty stack state of the result is different. 
	 * 
	 * @param nwa
	 * @throws AutomataOperationCanceledException
	 */
	public ReachableStatesCopy(final AutomataLibraryServices services,
			final INestedWordAutomatonSimple<LETTER,STATE> nwa,
			final boolean totalize, final boolean complement,
			final boolean removeDeadEnds, final boolean removeNonLiveStates)
			throws AutomataOperationCanceledException {
		super(services);
		if (complement && !totalize) {
			throw new IllegalArgumentException("complement requires totalize");
		}
		mComplement = complement;
		mInput = nwa;
		mLogger.info(startMessage());
		mTraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				mServices,
				nwa.getInternalAlphabet(), nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(), nwa.getStateFactory());
		super.mRemoveDeadEnds = removeDeadEnds;
		super.mRemoveNonLiveStates = removeNonLiveStates;
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.mTraversedNwa).setUp2Down(getUp2DownMapping());
		if (totalize || (! mInput.getInitialStates().iterator().hasNext())) {
			makeAutomatonTotal();
		}
		mLogger.info(exitMessage());
//		assert (new DownStateConsistencyCheck<LETTER, STATE>(mServices, 
//				(IDoubleDeckerAutomaton) mTraversedNwa)).getResult() : "down states inconsistent";
	}
	
	
	public ReachableStatesCopy(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER,STATE> nwa)
			throws AutomataLibraryException {
		super(services);
		mInput = nwa;
		mLogger.info(startMessage());
		mTraversedNwa = new DoubleDeckerAutomaton<LETTER,STATE>(
				mServices,
				nwa.getInternalAlphabet(), nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(), nwa.getStateFactory());
		super.mRemoveDeadEnds = false;
		super.mRemoveNonLiveStates = false;
		mComplement = false;
		traverseDoubleDeckerGraph();
		((DoubleDeckerAutomaton<LETTER,STATE>) super.mTraversedNwa).setUp2Down(getUp2DownMapping());
		mLogger.info(exitMessage());
//		assert (new DownStateConsistencyCheck<LETTER, STATE>(mServices, 
//				(IDoubleDeckerAutomaton) mTraversedNwa)).getResult() : "down states inconsistent";
	}
	
	private void makeAutomatonTotal() {
		final STATE sinkState = mTraversedNwa.getStateFactory().createSinkStateContent();
		final boolean isInitial = false; //mInput.getInitial().isEmpty();
		final boolean isFinal = mComplement;
		((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isFinal, sinkState);
		
		for (final STATE state : mTraversedNwa.getStates()) {
			for (final LETTER letter : mTraversedNwa.getInternalAlphabet()) {				
				if (!mTraversedNwa.internalSuccessors(state,letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(state, letter, sinkState);
				}
			}
			for (final LETTER letter : mTraversedNwa.getCallAlphabet()) {				
				if (!mTraversedNwa.callSuccessors(state,letter).iterator().hasNext()) {
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(state, letter, sinkState);
				}
			}
			for (final LETTER symbol : mTraversedNwa.getReturnAlphabet()) {
				for (final STATE hier : mTraversedNwa.getStates()) {
					if (!mTraversedNwa.returnSuccessors(state,hier,symbol).iterator().hasNext()) {
						((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(state, hier, symbol, sinkState);
					}
				}
			}
		}
	}

	@Override
	public String operationName() {
		return "reachableStatesCopy";
	}

	@Override
	public String startMessage() {
		return "Start " + operationName() + ". Input "
				+ mInput.sizeInformation();
	}

	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result "
				+ mTraversedNwa.sizeInformation();
	}

	@Override
	protected Collection<STATE> getInitialStates() {
//		final Collection<STATE> newInitialStates = new ArrayList<STATE>(mInput.getInitialStates().size());
		final Collection<STATE> newInitialStates = new ArrayList<STATE>();
		for (final STATE oldUpState : mInput.getInitialStates()) {
			final STATE newState = constructOrGetResState(oldUpState, true);
			newInitialStates.add(newState);
		}
		return newInitialStates;
	}

	private STATE constructOrGetResState(final STATE oldUp, final boolean isInitial) {
		if (mold2new.containsKey(oldUp)) {
			return mold2new.get(oldUp);
		}
		STATE newState = mold2new.get(oldUp);
		if (newState == null) {
			newState = oldUp;
			final boolean isAccepting = mInput.isFinal(oldUp) ^ mComplement;
			((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isAccepting, newState);
			mold2new.put(oldUp, newState);
			mnew2old.put(newState, oldUp);
		}
		return newState;

	}

	@Override
	protected Collection<STATE> buildInternalSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<STATE>();
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mnew2old.get(newUpState);
		for (final LETTER symbol : mInput.lettersInternal(oldUpState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans :
					mInput.internalSuccessors(oldUpState, symbol)) {
				final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	protected Collection<STATE> buildReturnSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<STATE>();
		final STATE newDownState = doubleDecker.getDown();
		if (newDownState == mTraversedNwa.getEmptyStackState()) {
			return succs;
		}
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mnew2old.get(newUpState);
		final STATE oldDownState = mnew2old.get(newDownState);

		for (final LETTER symbol : mInput.lettersReturn(oldUpState)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans :
					mInput.returnSuccessors(oldUpState, oldDownState, symbol)) {
				final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(newUpState, newDownState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}

	@Override
	protected Collection<STATE> buildCallSuccessors(final DoubleDecker<STATE> doubleDecker) {
		final ArrayList<STATE> succs = new ArrayList<STATE>();
		final STATE newUpState = doubleDecker.getUp();
		final STATE oldUpState = mnew2old.get(newUpState);
		for (final LETTER symbol : mInput.lettersCall(oldUpState)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans :
					mInput.callSuccessors(oldUpState, symbol)) {
				final STATE newSucc = constructOrGetResState(trans.getSucc(), false);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(newUpState, symbol, newSucc);
				succs.add(newSucc);
			}
		}
		return succs;
	}
	
	
	@Override
	public final INestedWordAutomaton<LETTER,STATE> getResult() throws AutomataOperationCanceledException {
		return mTraversedNwa;
	}


	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		
		boolean correct = true;
		if (!mRemoveNonLiveStates) {
			mLogger.info("Start testing correctness of " + operationName());
			if (!mComplement) {
				correct &= new IsIncluded<>(mServices, stateFactory, mInput, mTraversedNwa).getResult();
				correct &= new IsIncluded<>(mServices, stateFactory, mTraversedNwa, mInput).getResult();
				if (!correct) {
					ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mTraversedNwa);
				}
			} else {
				// intersection of operand and result should be empty
				final INestedWordAutomaton<LETTER, STATE> intersectionOperandResult = 
						(new IntersectDD<LETTER, STATE>(mServices, mInput, mTraversedNwa)).getResult();
				correct &= (new IsEmpty<LETTER, STATE>(mServices, intersectionOperandResult)).getResult();
				final INestedWordAutomaton<LETTER, STATE> resultSadd = 
						(new ComplementDD<LETTER, STATE>(mServices, stateFactory, mInput)).getResult();
				// should recognize same language as old computation
				correct &= new IsIncluded<>(mServices, stateFactory, resultSadd, mTraversedNwa).getResult();
				correct &= new IsIncluded<>(mServices, stateFactory, mTraversedNwa, resultSadd).getResult();
				if (!correct) {
					ResultChecker.writeToFileIfPreferred(mServices, operationName() + "Failed", "", mTraversedNwa);
				}
			}
			mLogger.info("Finished testing correctness of " + operationName());
		}
		return correct;
	}


}
