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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.buchi;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryException;
import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.IOperation;
import de.uni_freiburg.informatik.ultimate.automata.ResultChecker;
import de.uni_freiburg.informatik.ultimate.automata.StateFactory;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDecker;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.IsTotal;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DoubleDeckerVisitor;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.ReachableStatesCopy;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;

/**
 * BNWA complementation that works only for deterministic Buchi automata.
 */

//FIXME: return in final part may take nonfinal state from stack

public class BuchiComplementDeterministic<LETTER, STATE> extends DoubleDeckerVisitor<LETTER, STATE>
		implements IOperation<LETTER, STATE> {
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final INestedWordAutomaton<LETTER, STATE> mTotalizedOperand;
	private final StateFactory<STATE> mContentFactory;
	
	private final HashMap<STATE, STATE> mNew2Old = new HashMap<STATE, STATE>();
	
	private final HashMap<STATE, STATE> mOld2Final = new HashMap<STATE, STATE>();
	private final HashMap<STATE, STATE> mOld2NonFinal = new HashMap<STATE, STATE>();
	
	@Override
	public String operationName() {
		return "buchiComplementDeterministic";
	}
	
	@Override
	public String startMessage() {
		return "Start " + operationName() + " Operand " + mOperand.sizeInformation();
	}
	
	@Override
	public String exitMessage() {
		return "Finished " + operationName() + " Result " + mTraversedNwa.sizeInformation();
	}
	
	public BuchiComplementDeterministic(final AutomataLibraryServices services,
			final INestedWordAutomaton<LETTER, STATE> nwa) throws AutomataLibraryException {
		super(services);
		mOperand = nwa;
		mContentFactory = mOperand.getStateFactory();
		mLogger.info(startMessage());
		if (new IsTotal<LETTER, STATE>(mServices, mOperand).getResult()) {
			mTotalizedOperand = mOperand;
		} else {
			mTotalizedOperand =
					new ReachableStatesCopy<LETTER, STATE>(mServices, nwa, true, false, false, false).getResult();
		}
		mTraversedNwa = new NestedWordAutomaton<LETTER, STATE>(
				mServices,
				nwa.getInternalAlphabet(),
				nwa.getCallAlphabet(),
				nwa.getReturnAlphabet(),
				nwa.getStateFactory());
		traverseDoubleDeckerGraph();
		mLogger.info(exitMessage());
		
	}
	
	@Override
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mTraversedNwa;
	}
	
	STATE getOrConstructNewState(final STATE oldState, final boolean isInitial, final boolean isFinal) {
		STATE newState = isFinal
				? mOld2Final.get(oldState)
				: mOld2NonFinal.get(oldState);
		if (newState == null) {
			if (isFinal) {
				newState = mContentFactory.complementBuchiDeterministicFinal(oldState);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isFinal, newState);
				mOld2Final.put(oldState, newState);
			} else {
				newState = mContentFactory.complementBuchiDeterministicNonFinal(oldState);
				((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addState(isInitial, isFinal, newState);
				mOld2NonFinal.put(oldState, newState);
			}
			mNew2Old.put(newState, oldState);
		}
		return newState;
	}
	
	@Override
	protected Collection<STATE> getInitialStates() {
		final Collection<STATE> oldInitialStates =
				mTotalizedOperand.getInitialStates();
		assert (oldInitialStates.size() == 1);
		STATE oldInit = null;
		for (final STATE state : mTotalizedOperand.getInitialStates()) {
			oldInit = state;
		}
		final STATE newInit = getOrConstructNewState(oldInit, true, false);
		final ArrayList<STATE> newInitialStates = new ArrayList<STATE>(1);
		newInitialStates.add(newInit);
		return newInitialStates;
	}
	
	@Override
	protected Collection<STATE> visitAndGetCallSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final Collection<STATE> newSuccs = new ArrayList<STATE>();
		final STATE newState = doubleDecker.getUp();
		final boolean isFinal = mTraversedNwa.isFinal(newState);
		final STATE oldState = mNew2Old.get(newState);
		for (final LETTER symbol : mTotalizedOperand.lettersCall(oldState)) {
			for (final OutgoingCallTransition<LETTER, STATE> trans : mTotalizedOperand.callSuccessors(oldState,
					symbol)) {
				final STATE succ = trans.getSucc();
				if (!isFinal) {
					final STATE newSuccNonFinal = getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(newState, symbol,
							newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if (!mTotalizedOperand.isFinal(succ)) {
					final STATE newSuccFinal = getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addCallTransition(newState, symbol,
							newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}
	
	@Override
	protected Collection<STATE> visitAndGetInternalSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final Collection<STATE> newSuccs = new ArrayList<STATE>();
		final STATE newState = doubleDecker.getUp();
		final boolean isFinal = mTraversedNwa.isFinal(newState);
		final STATE oldState = mNew2Old.get(newState);
		for (final LETTER symbol : mTotalizedOperand.lettersInternal(oldState)) {
			for (final OutgoingInternalTransition<LETTER, STATE> trans : mTotalizedOperand.internalSuccessors(oldState,
					symbol)) {
				final STATE succ = trans.getSucc();
				if (!isFinal) {
					final STATE newSuccNonFinal = getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(newState, symbol,
							newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if (!mTotalizedOperand.isFinal(succ)) {
					final STATE newSuccFinal = getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addInternalTransition(newState, symbol,
							newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}
	
	@Override
	protected Collection<STATE> visitAndGetReturnSuccessors(
			final DoubleDecker<STATE> doubleDecker) {
		final Collection<STATE> newSuccs = new ArrayList<STATE>();
		final STATE newHier = doubleDecker.getDown();
		if (newHier == mTraversedNwa.getEmptyStackState()) {
			return newSuccs;
		}
		final STATE oldHier = mNew2Old.get(newHier);
		
		final STATE newState = doubleDecker.getUp();
		final boolean isFinal = mTraversedNwa.isFinal(newState);
		final STATE oldState = mNew2Old.get(newState);
		for (final LETTER symbol : mTotalizedOperand.lettersReturn(oldState)) {
			for (final OutgoingReturnTransition<LETTER, STATE> trans : mTotalizedOperand.returnSuccessors(oldState,
					oldHier, symbol)) {
				final STATE succ = trans.getSucc();
				if (!isFinal) {
					final STATE newSuccNonFinal =
							getOrConstructNewState(succ, false, false);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(newState, newHier, symbol,
							newSuccNonFinal);
					newSuccs.add(newSuccNonFinal);
				}
				if (!mTotalizedOperand.isFinal(succ)) {
					final STATE newSuccFinal =
							getOrConstructNewState(succ, false, true);
					((NestedWordAutomaton<LETTER, STATE>) mTraversedNwa).addReturnTransition(newState, newHier, symbol,
							newSuccFinal);
					newSuccs.add(newSuccFinal);
				}
			}
		}
		return newSuccs;
	}
	
	@Override
	public boolean checkResult(final StateFactory<STATE> stateFactory)
			throws AutomataLibraryException {
		return ResultChecker.buchiComplement(mServices, mOperand, mTraversedNwa);
	}
	
}
