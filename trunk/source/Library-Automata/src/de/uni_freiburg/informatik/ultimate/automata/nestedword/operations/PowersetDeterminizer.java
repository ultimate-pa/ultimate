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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations;

import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomatonSimple;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DeterminizedState;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;

/**
 * Construct deterministic states like in the classical powerset construction.
 * For determinization of NWAs there is also a powerset construction. This
 * class implements the computation of deterministic successor states according
 * to this powerset construction.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Symbol
 * @param <STATE>
 *            Content
 */
public class PowersetDeterminizer<LETTER, STATE> implements IStateDeterminizer<LETTER, STATE> {
	private final IStateFactory<STATE> mStateFactory;
	private final INestedWordAutomatonSimple<LETTER, STATE> mOperand;
	private final boolean mUseDoubleDeckers;
	private int mMaxDegreeOfNondeterminism;
	
	/**
	 * Constructor.
	 * 
	 * @param operand
	 *            operand
	 * @param useDoubleDeckers
	 *            true iff double deckers should be used
	 * @param stateFactory
	 *            state factory
	 */
	public PowersetDeterminizer(final INestedWordAutomatonSimple<LETTER, STATE> operand, final boolean useDoubleDeckers,
			final IStateFactory<STATE> stateFactory) {
		mOperand = operand;
		mUseDoubleDeckers = useDoubleDeckers;
		this.mStateFactory = stateFactory;
	}
	
	@Override
	public DeterminizedState<LETTER, STATE> initialState() {
		final DeterminizedState<LETTER, STATE> detState = new DeterminizedState<>(mOperand);
		for (final STATE initialState : mOperand.getInitialStates()) {
			detState.addPair(mOperand.getEmptyStackState(), initialState, mOperand);
		}
		updateMaxDegreeOfNondeterminism(detState.degreeOfNondeterminism());
		return detState;
	}
	
	@Override
	public DeterminizedState<LETTER, STATE> internalSuccessor(
			final DeterminizedState<LETTER, STATE> detState,
			final LETTER symbol) {
		
		final DeterminizedState<LETTER, STATE> succDetState = new DeterminizedState<>(mOperand);
		for (final STATE downState : detState.getDownStates()) {
			for (final STATE upState : detState.getUpStates(downState)) {
				for (final OutgoingInternalTransition<LETTER, STATE> upSucc : mOperand.internalSuccessors(upState,
						symbol)) {
					succDetState.addPair(downState, upSucc.getSucc(), mOperand);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;
	}
	
	@Override
	public DeterminizedState<LETTER, STATE> callSuccessor(final DeterminizedState<LETTER, STATE> detState,
			final LETTER symbol) {
		
		final DeterminizedState<LETTER, STATE> succDetState = new DeterminizedState<>(mOperand);
		for (final STATE downState : detState.getDownStates()) {
			for (final STATE upState : detState.getUpStates(downState)) {
				for (final OutgoingCallTransition<LETTER, STATE> upSucc : mOperand.callSuccessors(upState, symbol)) {
					// if !mUseDoubleDeckers we always use getEmptyStackState()
					// as down state to obtain sets of states instead of
					// sets of DoubleDeckers.
					final STATE succDownState = mUseDoubleDeckers ? upState : mOperand.getEmptyStackState();
					succDetState.addPair(succDownState, upSucc.getSucc(), mOperand);
				}
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;
	}
	
	@Override
	public DeterminizedState<LETTER, STATE> returnSuccessor(final DeterminizedState<LETTER, STATE> detState,
			final DeterminizedState<LETTER, STATE> detLinPred, final LETTER symbol) {
		
		final DeterminizedState<LETTER, STATE> succDetState = new DeterminizedState<>(mOperand);
		
		for (final STATE downLinPred : detLinPred.getDownStates()) {
			for (final STATE upLinPred : detLinPred.getUpStates(downLinPred)) {
				returnSuccessorsHelper(detState, symbol, succDetState, downLinPred, upLinPred);
			}
		}
		updateMaxDegreeOfNondeterminism(succDetState.degreeOfNondeterminism());
		return succDetState;
	}

	@SuppressWarnings("squid:S1698")
	private void returnSuccessorsHelper(final DeterminizedState<LETTER, STATE> detState, final LETTER symbol,
			final DeterminizedState<LETTER, STATE> succDetState, final STATE downLinPred, final STATE upLinPred) {
		Set<STATE> upStates;
		if (mUseDoubleDeckers) {
			upStates = detState.getUpStates(upLinPred);
			if (upStates == null) {
				return;
			}
		} else {
			assert detState.getDownStates().size() == 1;
			// equality intended here
			assert detState.getDownStates().iterator().next() == mOperand.getEmptyStackState();
			// if !mUseDoubleDeckers we always use getEmptyStackState()
			// as down state to obtain sets of states instead of
			// sets of DoubleDeckers.
			upStates = detState.getUpStates(mOperand.getEmptyStackState());
		}
		for (final STATE upState : upStates) {
			for (final OutgoingReturnTransition<LETTER, STATE> upSucc : mOperand.returnSuccessors(upState,
					upLinPred, symbol)) {
				// equality intended here
				assert mUseDoubleDeckers || downLinPred == mOperand.getEmptyStackState();
				succDetState.addPair(downLinPred, upSucc.getSucc(), mOperand);
			}
		}
	}
	
	private void updateMaxDegreeOfNondeterminism(final int newDegree) {
		if (newDegree > mMaxDegreeOfNondeterminism) {
			mMaxDegreeOfNondeterminism = newDegree;
		}
	}
	
	@Override
	public int getMaxDegreeOfNondeterminism() {
		return mMaxDegreeOfNondeterminism;
	}
	
	@Override
	public boolean useDoubleDeckers() {
		return mUseDoubleDeckers;
	}
	
	@Override
	public STATE getState(final DeterminizedState<LETTER, STATE> determinizedState) {
		return determinizedState.getContent(mStateFactory);
	}
}
