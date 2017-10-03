/*
 * Copyright (C) 2017 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
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

import java.util.HashMap;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.SetOfStates;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IRelabelStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.TransformIterator;

/**
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            Type of objects which can be used as letters of the alphabet.
 * @param <STATE>
 *            Type of objects which can be used as states.
 */
public class RelabelNwa<LETTER, STATE> implements INwaOutgoingTransitionProvider<LETTER, STATE> {

	private final IRelabelStateFactory<STATE> mStateFactory;
	private final INwaOutgoingTransitionProvider<LETTER, STATE> mOperand;
	private final ConstructionCache<STATE, STATE> mNewStateCache;
	private final Map<STATE, STATE> mNewState2OldState;

	private final SetOfStates<STATE> mSetOfStates;

	private final Function<OutgoingInternalTransition<LETTER, STATE>, OutgoingInternalTransition<LETTER, STATE>> mInternalTransitionTransformer;
	private final Function<OutgoingCallTransition<LETTER, STATE>, OutgoingCallTransition<LETTER, STATE>> mCallTransitionTransformer;
	private final Function<OutgoingReturnTransition<LETTER, STATE>, OutgoingReturnTransition<LETTER, STATE>> mReturnTransitionTransformer;

	public RelabelNwa(final IRelabelStateFactory<STATE> stateFactory,
			final INwaOutgoingTransitionProvider<LETTER, STATE> operand) {
		super();
		mStateFactory = stateFactory;
		mOperand = operand;
		mNewState2OldState = new HashMap<>();
		final IValueConstruction<STATE, STATE> valueConstruction = new IValueConstruction<STATE, STATE>() {
			int mStateCounter = 0;

			@Override
			public STATE constructValue(final STATE oldState) {
				final STATE newState = stateFactory.relabel(oldState, mStateCounter);
				mStateCounter++;
				final STATE oldValue = mNewState2OldState.put(newState, oldState);
				if (oldValue != null) {
					throw new AssertionError("double state " + oldValue);
				}
				final boolean isInitial = mOperand.isInitial(oldState);
				final boolean isAccepting = mOperand.isFinal(oldState);
				
				mSetOfStates.addState(isInitial, isAccepting, newState);
				return newState;
			}

		};
		mNewStateCache = new ConstructionCache<>(valueConstruction);

		mInternalTransitionTransformer = (x -> new OutgoingInternalTransition<LETTER, STATE>(x.getLetter(),
				mNewStateCache.getOrConstruct(x.getSucc())));
		mCallTransitionTransformer = (x -> new OutgoingCallTransition<LETTER, STATE>(x.getLetter(),
				mNewStateCache.getOrConstruct(x.getSucc())));
		mReturnTransitionTransformer = (x -> new OutgoingReturnTransition<LETTER, STATE>(
				mNewStateCache.getOrConstruct(x.getHierPred()), x.getLetter(),
				mNewStateCache.getOrConstruct(x.getSucc())));

		final STATE newEmptyStackState = stateFactory.createEmptyStackState();
		mSetOfStates = new SetOfStates<STATE>(newEmptyStackState);
		for (final STATE oldInitialState : mOperand.getInitialStates()) {
			mNewStateCache.getOrConstruct(oldInitialState);
		}

	}

	@Override
	public Set<LETTER> getAlphabet() {
		return mOperand.getAlphabet();
	}

	@Override
	public IStateFactory<STATE> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public int size() {
		return mOperand.size();
	}

	@Override
	public String sizeInformation() {
		return mOperand.sizeInformation();
	}

	@Override
	public VpAlphabet<LETTER> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public STATE getEmptyStackState() {
		return mSetOfStates.getEmptyStackState();
	}

	@Override
	public Iterable<STATE> getInitialStates() {
		return mSetOfStates.getInitialStates();
	}

	@Override
	public boolean isInitial(final STATE state) {
		return mSetOfStates.isInitial(state);
	}

	@Override
	public boolean isFinal(final STATE state) {
		return mSetOfStates.isAccepting(state);
	}

	@Override
	public Iterable<OutgoingInternalTransition<LETTER, STATE>> internalSuccessors(final STATE state) {
		final STATE oldState = mNewState2OldState.get(state);
		return () -> new TransformIterator<OutgoingInternalTransition<LETTER, STATE>, OutgoingInternalTransition<LETTER, STATE>>(
				mOperand.internalSuccessors(oldState).iterator(), mInternalTransitionTransformer);
	}

	@Override
	public Iterable<OutgoingCallTransition<LETTER, STATE>> callSuccessors(final STATE state) {
		final STATE oldState = mNewState2OldState.get(state);
		return () -> new TransformIterator<OutgoingCallTransition<LETTER, STATE>, OutgoingCallTransition<LETTER, STATE>>(
				mOperand.callSuccessors(oldState).iterator(), mCallTransitionTransformer);
	}

	@Override
	public Iterable<OutgoingReturnTransition<LETTER, STATE>> returnSuccessorsGivenHier(final STATE state,
			final STATE hier) {
		final STATE oldState = mNewState2OldState.get(state);
		final STATE oldHier = mNewState2OldState.get(hier);
		return () -> new TransformIterator<OutgoingReturnTransition<LETTER, STATE>, OutgoingReturnTransition<LETTER, STATE>>(
				mOperand.returnSuccessorsGivenHier(oldState, oldHier).iterator(), mReturnTransitionTransformer);
	}

}
