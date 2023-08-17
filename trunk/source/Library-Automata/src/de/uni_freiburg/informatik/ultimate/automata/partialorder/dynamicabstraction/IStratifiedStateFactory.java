/*
 * Copyright (C) 2023 Veronika Klasen
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import java.util.LinkedList;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Interface for the state factory used for the dynamic stratified reduction.
 *
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the original automaton
 * @param <R>
 *            The type of states in the reduced automaton, consists of an original, a sleep set, an abstraction level,
 *            an upper limit for the abstraction level and a list of predecessors of the state that are safe to loop
 *            back to
 * @param <H>
 *            The type of abstraction level used in the reduction automaton
 */

public interface IStratifiedStateFactory<L, S, R, H> extends IEmptyStackStateFactory<R> {
	// Method to create a reduction state
	R createStratifiedState(S state, ImmutableSet<L> sleepset, H level, H limit, LinkedList<R> loopPredecs);

	// Returns the original state from which a reduction state was constructed
	S getOriginalState(R state);

	// Returns the sleep set of a reduction state
	ImmutableSet<L> getSleepSet(R state);

	// Returns the abstraction level of a reduction state
	H getAbstractionLevel(R state);

	// Add additional variables to the abstraction level of a state
	void addToAbstractionLevel(R state, Set<L> variables);

	// Returns the abstraction limit of a reduction state (is the upper limit for the abstraction level of all reduction
	// states reachable from state)
	H getAbstractionLimit(R state);

	// Add additional variables to the abstraction level of a state
	void addToAbstractionLimit(R state, Set<L> variables);

	// Returns the set of predecessors that state is allowed to loop back to
	LinkedList<R> getLoopablePredecs(R state);

	boolean isLoopCopy(final R state);
}

/**
 * Class implementing the interface, uses the standard (and only existing) type of dynamic stratified reduction state
 * and abstraction level.
 *
 *
 * @param <L>
 *            Type of letter of the original automaton
 * @param <S>
 *            Type of state of the original automaton
 */

class StratifiedStateFactory<L, S>
		implements IStratifiedStateFactory<L, S, StratifiedReductionState<L, S>, AbstractionLevel<L>> {

	// Wir wollen nicht wirklich einen Kellerautomaten
	@Override
	public StratifiedReductionState<L, S> createEmptyStackState() {
		// TODO Find out the right type for this
		throw new UnsupportedOperationException();
	}

	@Override
	public StratifiedReductionState<L, S> createStratifiedState(final S state, final ImmutableSet<L> sleepset,
			final AbstractionLevel<L> level, final AbstractionLevel<L> limit,
			final LinkedList<StratifiedReductionState<L, S>> loopPredecs) {

		return new StratifiedReductionState<>(state, sleepset, level, limit, loopPredecs);
	}

	@Override
	public S getOriginalState(final StratifiedReductionState<L, S> state) {
		return state.mOriginalState;
	}

	@Override
	public ImmutableSet<L> getSleepSet(final StratifiedReductionState<L, S> state) {
		return state.mSleepSet;
	}

	@Override
	public AbstractionLevel<L> getAbstractionLevel(final StratifiedReductionState<L, S> state) {
		return state.mAbstractionLevel;
	}

	@Override
	public void addToAbstractionLevel(final StratifiedReductionState<L, S> state, final Set<L> variables) {
		state.mAbstractionLevel.addToAbstractionLevel(variables);

	}

	@Override
	public AbstractionLevel<L> getAbstractionLimit(final StratifiedReductionState<L, S> state) {
		return state.mAbstractionLimit;
	}

	@Override
	public void addToAbstractionLimit(final StratifiedReductionState<L, S> state, final Set<L> variables) {
		state.mAbstractionLimit.addToAbstractionLevel(variables);
	}

	@Override
	public LinkedList<StratifiedReductionState<L, S>> getLoopablePredecs(final StratifiedReductionState<L, S> state) {
		return state.mLoopablePredecs;
	}

	@Override
	public boolean isLoopCopy(final StratifiedReductionState<L, S> state) {
		return state.mAbstractionLimit.isLocked();
	}
}

/**
 * create a state of the reduction automaton for dynamic stratified reduction
 *
 * @param originalState
 *            state of the input automaton
 * @param sleepSet
 *            a given set of letters
 * @param abstractionLevel
 *            an object with a set of program variables 'value' and a boolean 'locked' locked = true means that the
 *            abstraction level is fully defined and no more variables will be added to its value
 * @param abstractionLimit
 *            an object with a set of program variables 'value' and a boolean 'locked' locked = true means that the
 *            state with this abstraction limit is part of a loop copy with this abstraction limit
 *
 * @return the corresponding state of the reduction automaton
 */

class StratifiedReductionState<L, S> {
	// TODO: I'd like for its state factory to be the only 'friend' of this class
	protected S mOriginalState;
	protected ImmutableSet<L> mSleepSet;
	protected AbstractionLevel<L> mAbstractionLevel;
	protected AbstractionLevel<L> mAbstractionLimit; // does this need to be an AbstractionLevel?
	protected LinkedList<StratifiedReductionState<L, S>> mLoopablePredecs;

	public StratifiedReductionState(final S state, final ImmutableSet<L> sleepset, final AbstractionLevel<L> absLv,
			final AbstractionLevel<L> absLmt, final LinkedList<StratifiedReductionState<L, S>> loopPredecs) {
		assert absLv.isLEQ(absLmt) : "Abstraction level is bigger than the allowed upper limit!";
		mOriginalState = state;
		mSleepSet = sleepset;
		mAbstractionLevel = absLv;
		mAbstractionLimit = absLmt;
		mLoopablePredecs = loopPredecs;
	}
}
