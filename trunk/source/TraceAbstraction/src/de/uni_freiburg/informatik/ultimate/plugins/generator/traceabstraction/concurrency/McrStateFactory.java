/*
 * Copyright (C) 2021-2022 Dennis Wölfing
 * Copyright (C) 2021-2022 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IMLPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.IPredicate;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.predicates.PredicateFactory;

/**
 * A factory for MCR automaton states.
 *
 * @author Dennis Wölfing
 *
 * @param <L>
 *            The type of the letters in the automaton.
 */
public class McrStateFactory<L extends IIcfgTransition<?>> implements IEmptyStackStateFactory<IPredicate> {
	private final IPredicate mEmptyStack;
	private final boolean mUseDependencyRanks;
	private final HashMap<IMcrState<L>, IMcrState<L>> mStates;

	/**
	 * Creates the factory.
	 *
	 * @param factory
	 *            A PredicateFactory.
	 * @param useDependencyRanks
	 *            true if the dependency ranks should be used.
	 */
	public McrStateFactory(final PredicateFactory factory, final boolean useDependencyRanks) {
		mEmptyStack = factory.newEmptyStackPredicate();
		mUseDependencyRanks = useDependencyRanks;
		mStates = new HashMap<>();
	}

	/**
	 * Creates the initial state of the representative automaton from the initial state of the original automaton.
	 *
	 * @param initial
	 *            The original state from the input automaton.
	 * @return A new state of the representative automaton.
	 */
	public IMcrState<L> createState(final IPredicate initial) {
		if (!(initial instanceof IMLPredicate)) {
			throw new IllegalArgumentException("Unexpected type of predicate: " + initial.getClass());
		}
		IMcrState<L> state;
		if (mUseDependencyRanks) {
			state = new McrState<>((IMLPredicate) initial);
		} else {
			state = new McrState2<>((IMLPredicate) initial);
		}

		if (mStates.containsKey(state)) {
			return mStates.get(state);
		}
		mStates.put(state, state);
		return state;
	}

	/**
	 * Creates the next state of the representative automaton after executing a given transtion.
	 *
	 * @param state
	 *            The starting state of the representative automaton.
	 * @param transition
	 *            The transition to take.
	 * @param successorState
	 *            The successor state in the original automaton after taking the transition.
	 * @return The new state of the representative automton, or null if the transition should be omitted.
	 */
	public IMcrState<L> createNextState(final IMcrState<L> state, final L transition,
			final IMLPredicate successorState) {
		final IMcrState<L> newState = state.getNextState(transition, successorState);
		if (newState == null) {
			return null;
		}
		if (mStates.containsKey(newState)) {
			return mStates.get(newState);
		}
		mStates.put(newState, newState);
		return newState;
	}

	@Override
	public IPredicate createEmptyStackState() {
		return mEmptyStack;
	}

	/**
	 * Gets the original state of a state constructed by this factory.
	 *
	 * @param state
	 *            An MCR state.
	 * @return The state in the original automaton.
	 */
	public IPredicate getOriginalState(final IPredicate state) {
		assert state instanceof IMcrState<?>;
		return ((IMcrState<?>) state).getOldState();
	}

	public int getNumberOfConstructedStates() {
		return mStates.size();
	}

	/**
	 * Resets the factory. Any states constructed by the factory will be forgotten.
	 */
	public void reset() {
		mStates.clear();
	}
}
