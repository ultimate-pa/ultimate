/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization;

import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.DoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.IDoubleDeckerAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomaton;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IBlock;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.util.IPartition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.oldapi.DoubleDeckerVisitor.ReachFinal;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IMergeStateFactory;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache;
import de.uni_freiburg.informatik.ultimate.util.ConstructionCache.IValueConstruction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.UnionFind;

/**
 * Constructs the quotient for a given nested word automaton and an equivalence relation on its states.
 * <p>
 * The equivalence relation has to be given as a {@link UnionFind} or a {@link IPartition} data structure.
 * <p>
 * If the operand is an {@link IDoubleDeckerAutomaton}, the output will also be an {@link IDoubleDeckerAutomaton}.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <LETTER>
 *            letter type
 * @param <STATE>
 *            state type
 */
public class QuotientNwaConstructor<LETTER, STATE> {
	private final AutomataLibraryServices mServices;
	private final IMergeStateFactory<STATE> mStateFactory;
	private final INestedWordAutomaton<LETTER, STATE> mOperand;
	private final NestedWordAutomaton<LETTER, STATE> mResult;
	private GetOnlyMap mOldState2NewState;

	private final STATE mOldEmptyStackState;
	private final STATE mNewEmptyStackState;

	private final Map<STATE, Map<STATE, ReachFinal>> mUp2Down;

	/**
	 * Private constructor for common parts.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand automaton
	 * @param newSize
	 *            size of new (to be constructed) automaton
	 */
	private <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> QuotientNwaConstructor(
			final AutomataLibraryServices services, final FACTORY stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final int newSize) {
		mServices = services;
		mStateFactory = stateFactory;
		mOperand = operand;

		if (operand instanceof IDoubleDeckerAutomaton<?, ?>) {
			// create a DoubleDeckerAutomaton
			mResult = new DoubleDeckerAutomaton<>(mServices, mOperand.getInternalAlphabet(), mOperand.getCallAlphabet(),
					mOperand.getReturnAlphabet(), mStateFactory);
			mUp2Down = new HashMap<>(newSize);
			((DoubleDeckerAutomaton<LETTER, STATE>) mResult).setUp2Down(mUp2Down);
		} else {
			// create a NestedWordAutomaton
			mResult = new NestedWordAutomaton<>(mServices, mOperand.getInternalAlphabet(), mOperand.getCallAlphabet(),
					mOperand.getReturnAlphabet(), mStateFactory);
			mUp2Down = null;
		}

		mOldEmptyStackState = mOperand.getEmptyStackState();
		mNewEmptyStackState = stateFactory.createEmptyStackState();
	}

	/**
	 * Constructor with partition data structure.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand automaton
	 * @param partition
	 *            partition data structure
	 * @param addMapOldState2newState
	 *            add a map from old to new states?
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> QuotientNwaConstructor(
			final AutomataLibraryServices services, final FACTORY stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final IPartition<STATE> partition,
			final boolean addMapOldState2newState) {
		this(services, stateFactory, operand, partition.size());

		final ResultStateConstructorFromPartition resStateConstructor =
				new ResultStateConstructorFromPartition(partition);
		constructResultPartition(resStateConstructor, partition);
		mOldState2NewState = addMapOldState2newState ? new GetOnlyMap(resStateConstructor) : null;
	}

	/**
	 * Constructor with union-find data structure.
	 * 
	 * @param services
	 *            Ultimate services
	 * @param stateFactory
	 *            state factory
	 * @param operand
	 *            operand automaton
	 * @param unionFind
	 *            union-find data structure
	 * @param addMapOldState2newState
	 *            add a map from old to new states?
	 */
	public <FACTORY extends IMergeStateFactory<STATE> & IEmptyStackStateFactory<STATE>> QuotientNwaConstructor(
			final AutomataLibraryServices services, final FACTORY stateFactory,
			final INestedWordAutomaton<LETTER, STATE> operand, final UnionFind<STATE> unionFind,
			final boolean addMapOldState2newState) {
		this(services, stateFactory, operand, unionFind.size());

		final ResultStateConstructorFromUnionFind resStateConstructor =
				new ResultStateConstructorFromUnionFind(unionFind);
		constructResultUnionFind(resStateConstructor);
		mOldState2NewState = addMapOldState2newState ? new GetOnlyMap(resStateConstructor) : null;
	}

	/**
	 * Constructs the result automaton from a union-find data structure.
	 * 
	 * @param resStateConstructor
	 *            state constructor
	 */
	private void constructResultUnionFind(final IResultStateConstructor<STATE> resStateConstructor) {
		for (final STATE inputState : mOperand.getStates()) {
			constructStateAndSuccessors(resStateConstructor, inputState, false);
		}
	}

	/**
	 * Constructs the result automaton from a partition data structure.
	 * 
	 * @param resStateConstructor
	 *            state constructor
	 * @param partition
	 *            partition
	 */
	private void constructResultPartition(final IResultStateConstructor<STATE> resStateConstructor,
			final IPartition<STATE> partition) {
		final Iterator<IBlock<STATE>> blocksIt = partition.blocksIterator();
		/*
		 * iterate over all blocks
		 * 
		 * NOTE: there needs not be any block for an empty automaton
		 */
		while (blocksIt.hasNext()) {
			final IBlock<STATE> block = blocksIt.next();
			final boolean isRepresentativeIndependent = block.isRepresentativeIndependentInternalsCalls();

			final Iterator<STATE> statesIt = block.statesIterator();
			assert statesIt.hasNext() : "There must be at least one state.";
			boolean pastFirst = false;
			// iterate over all states
			do {
				final STATE inputState = statesIt.next();
				final boolean skipInternalsCalls = isRepresentativeIndependent && pastFirst;
				constructStateAndSuccessors(resStateConstructor, inputState, skipInternalsCalls);
				pastFirst = true;
			} while (statesIt.hasNext());
		}
	}

	/**
	 * Adds a state and all outgoing transitions for an input state.
	 * 
	 * @param resStateConstructor
	 *            state constructor
	 * @param inputState
	 *            input state
	 * @param skipInternalsCalls
	 *            true iff internal and call transitions can be
	 *            skipped
	 */
	private void constructStateAndSuccessors(final IResultStateConstructor<STATE> resStateConstructor,
			final STATE inputState, final boolean skipInternalsCalls) {
		// new state
		final STATE resultState = resStateConstructor.getOrConstructResultState(inputState);

		// get down state map
		if (mOperand instanceof IDoubleDeckerAutomaton<?, ?>) {
			addDownStates(resStateConstructor, inputState, resultState);
		}

		// new outgoing transitions
		if (!skipInternalsCalls) {
			// add internal and call transitions for
			addOutgoingTransitionsInternal(resStateConstructor, inputState, resultState);
			addOutgoingTransitionsCall(resStateConstructor, inputState, resultState);
		}
		addOutgoingTransitionsReturn(resStateConstructor, inputState, resultState);
	}

	@SuppressWarnings("squid:S1698")
	private void addDownStates(final IResultStateConstructor<STATE> resStateConstructor, final STATE inputState,
			final STATE resultState) {
		assert mOperand instanceof IDoubleDeckerAutomaton<?, ?>;
		assert mResult instanceof DoubleDeckerAutomaton<?, ?>;

		Map<STATE, ReachFinal> downStateMap = mUp2Down.get(resultState);
		if (downStateMap == null) {
			downStateMap = new HashMap<>();
			mUp2Down.put(resultState, downStateMap);
		}

		// add down states
		for (final STATE oldDownState : ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).getDownStates(inputState)) {
			// new state
			final STATE resultDownState;

			// equality intended here
			if (oldDownState == mOldEmptyStackState) {
				// empty stack symbol
				resultDownState = mNewEmptyStackState;
			} else {
				// "normal" stack symbol
				resultDownState = resStateConstructor.getOrConstructResultState(oldDownState);
			}

			// update map
			downStateMap.put(resultDownState, ReachFinal.UNKNOWN);
		}
	}

	/**
	 * @param resStateConstructor
	 *            The state constructor.
	 * @param inputState
	 *            state in input automaton
	 * @param resultState
	 *            state in output automaton
	 */
	private void addOutgoingTransitionsInternal(final IResultStateConstructor<STATE> resStateConstructor,
			final STATE inputState, final STATE resultState) {
		for (final OutgoingInternalTransition<LETTER, STATE> trans : mOperand.internalSuccessors(inputState)) {
			final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
			mResult.addInternalTransition(resultState, trans.getLetter(), resultSucc);
		}
	}

	/**
	 * @param resStateConstructor
	 *            The state constructor.
	 * @param inputState
	 *            state in input automaton
	 * @param resultState
	 *            state in output automaton
	 */
	private void addOutgoingTransitionsCall(final IResultStateConstructor<STATE> resStateConstructor,
			final STATE inputState, final STATE resultState) {
		for (final OutgoingCallTransition<LETTER, STATE> trans : mOperand.callSuccessors(inputState)) {
			final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
			mResult.addCallTransition(resultState, trans.getLetter(), resultSucc);
		}
	}

	/**
	 * @param resStateConstructor
	 *            The state constructor.
	 * @param inputState
	 *            state in input automaton
	 * @param resultState
	 *            state in output automaton
	 */
	private void addOutgoingTransitionsReturn(final IResultStateConstructor<STATE> resStateConstructor,
			final STATE inputState, final STATE resultState) {
		for (final OutgoingReturnTransition<LETTER, STATE> trans : mOperand.returnSuccessors(inputState)) {
			/*
			 * Return transitions which are not usable in the original automaton
			 * may change the language if they are blindly copied.
			 */
			assert (!(mOperand instanceof IDoubleDeckerAutomaton<?, ?>))
					|| ((IDoubleDeckerAutomaton<LETTER, STATE>) mOperand).isDoubleDecker(inputState,
							trans.getHierPred()) : "Unusable return transitions should not be present.";

			final STATE resultSucc = resStateConstructor.getOrConstructResultState(trans.getSucc());
			final STATE resultHierPred = resStateConstructor.getOrConstructResultState(trans.getHierPred());
			mResult.addReturnTransition(resultState, resultHierPred, trans.getLetter(), resultSucc);
		}
	}

	/**
	 * @return The quotient automaton.
	 */
	public INestedWordAutomaton<LETTER, STATE> getResult() {
		return mResult;
	}

	/**
	 * @return A map from input automaton states to output automaton states.
	 */
	public Map<STATE, STATE> getOldState2newState() {
		return mOldState2NewState;
	}

	/**
	 * Constructs the states of the resulting automaton (parametric in the data structure).
	 * 
	 * @param <STATE>
	 *            state tpe
	 */
	private interface IResultStateConstructor<STATE> {
		/**
		 * @param inputState
		 *            An state in the input automaton.
		 * @return new state in quotient automaton (constructed if not existent)
		 */
		STATE getOrConstructResultState(final STATE inputState);

		/**
		 * @param inputState
		 *            An state in the input automaton.
		 * @return new state in quotient automaton
		 */
		STATE get(final STATE inputState);
	}

	/**
	 * Result state constructor from a union-find data structure.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	@SuppressWarnings("squid:S1698")
	private class ResultStateConstructorFromUnionFind implements IResultStateConstructor<STATE> {
		private final ConstructionCache<STATE, STATE> mConstructionCache;
		private final UnionFind<STATE> mUnionFind;

		public ResultStateConstructorFromUnionFind(final UnionFind<STATE> unionFind) {
			mUnionFind = unionFind;
			final IValueConstruction<STATE, STATE> valueConstruction = new IValueConstruction<STATE, STATE>() {
				@Override
				public STATE constructValue(final STATE inputState) {
					final STATE representative = mUnionFind.find(inputState);
					assert (representative == inputState)
							|| (representative == null) : "must be representative or null";
					final STATE resultState;
					final boolean isInitial;
					final boolean isFinal;
					if (representative == null) {
						resultState = mStateFactory.merge(Collections.singleton(inputState));
						isInitial = mOperand.isInitial(inputState);
						isFinal = mOperand.isFinal(inputState);
					} else {
						final Collection<STATE> equivalenceClass =
								mUnionFind.getEquivalenceClassMembers(representative);
						resultState = mStateFactory.merge(equivalenceClass);
						final Predicate<STATE> pInitial = s -> mOperand.isInitial(s);
						isInitial = equivalenceClass.stream().anyMatch(pInitial);
						final Predicate<STATE> pFinal = s -> mOperand.isFinal(s);
						isFinal = equivalenceClass.stream().anyMatch(pFinal);
					}
					mResult.addState(isInitial, isFinal, resultState);
					return resultState;
				}
			};
			mConstructionCache = new ConstructionCache<>(valueConstruction);
		}

		@Override
		public STATE getOrConstructResultState(final STATE inputState) {
			STATE inputRepresentative = mUnionFind.find(inputState);
			if (inputRepresentative == null) {
				inputRepresentative = inputState;
			}
			return mConstructionCache.getOrConstruct(inputRepresentative);
		}

		@Override
		public STATE get(final STATE inputState) {
			STATE inputRepresentative = mUnionFind.find(inputState);
			if (inputRepresentative == null) {
				inputRepresentative = inputState;
			}
			return mConstructionCache.getMap().get(inputRepresentative);
		}
	}

	/**
	 * Result state constructor from a partition data structure.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class ResultStateConstructorFromPartition implements IResultStateConstructor<STATE> {
		private final ConstructionCache<IBlock<STATE>, STATE> mConstructionCache;
		private final IPartition<STATE> mPartition;

		public ResultStateConstructorFromPartition(final IPartition<STATE> partition) {
			mPartition = partition;

			final IValueConstruction<IBlock<STATE>, STATE> valueConstruction =
					new IValueConstruction<IBlock<STATE>, STATE>() {
						@Override
						public STATE constructValue(final IBlock<STATE> block) {
							final STATE resultState = block.minimize(mStateFactory);
							final boolean isInitial = block.isInitial();
							final boolean isFinal = block.isFinal();
							mResult.addState(isInitial, isFinal, resultState);
							return resultState;
						}
					};
			mConstructionCache = new ConstructionCache<>(valueConstruction);
		}

		@Override
		public STATE getOrConstructResultState(final STATE inputState) {
			final IBlock<STATE> block = mPartition.getBlock(inputState);
			assert block != null : "Block is not known.";
			return mConstructionCache.getOrConstruct(block);
		}

		@Override
		public STATE get(final STATE inputState) {
			final IBlock<STATE> block = mPartition.getBlock(inputState);
			return mConstructionCache.getMap().get(block);
		}
	}

	/**
	 * This map only supports the <code>get()</code> method.
	 * <p>
	 * We use it here for the map 'old state -> new state' as this is the only
	 * operation used later on.
	 * The reason why we use this map instead of a fresh one is that we create
	 * the backing data structure already during construction time.
	 * 
	 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
	 */
	private class GetOnlyMap implements Map<STATE, STATE> {
		private final IResultStateConstructor<STATE> mResStateConstructor;

		public GetOnlyMap(final IResultStateConstructor<STATE> resCons) {
			this.mResStateConstructor = resCons;
		}

		@Override
		public int size() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean isEmpty() {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsKey(final Object key) {
			throw new UnsupportedOperationException();
		}

		@Override
		public boolean containsValue(final Object value) {
			throw new UnsupportedOperationException();
		}

		@SuppressWarnings("unchecked")
		@Override
		public STATE get(final Object key) {
			return mResStateConstructor.get((STATE) key);
		}

		@Override
		public STATE put(final STATE key, final STATE value) {
			throw new UnsupportedOperationException();
		}

		@Override
		public STATE remove(final Object key) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void putAll(final Map<? extends STATE, ? extends STATE> map) {
			throw new UnsupportedOperationException();
		}

		@Override
		public void clear() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Set<STATE> keySet() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Collection<STATE> values() {
			throw new UnsupportedOperationException();
		}

		@Override
		public Set<Entry<STATE, STATE>> entrySet() {
			throw new UnsupportedOperationException();
		}
	}
}
