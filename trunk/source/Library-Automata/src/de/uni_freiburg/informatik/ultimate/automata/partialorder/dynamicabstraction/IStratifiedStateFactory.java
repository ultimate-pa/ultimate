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

import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.statefactory.IEmptyStackStateFactory;

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
 *            The type of abstraction level value used in the reduction automaton
 */

public interface IStratifiedStateFactory<L, S, R, H> extends IEmptyStackStateFactory<R> {
	/**
	 * Create a reduction state
	 *
	 * @param state
	 *            a state of the original automaton
	 * @param level
	 *            the reduction states abstraction level
	 * @param limit
	 *            the reduction states abstraction limit
	 * @return a state of the reduction automaton
	 */

	R createStratifiedState(S state, AbstractionLevel<H> level, AbstractionLevel<H> limit);

	/**
	 * Returns the original state from which a reduction state was constructed
	 *
	 * @param state
	 *            a state of the reduction automaton
	 *
	 * @return the state's original state
	 */
	S getOriginalState(R state);

	/**
	 * Returns the sleep set of a reduction state
	 *
	 * @param state
	 *            a state of the reduction automaton
	 * @return the state's sleep set
	 */
	Map<L, H> getSleepSet(R state);

	/**
	 * Set the sleep set of state to a set of variables
	 *
	 * @param state
	 *            whose sleep set is set
	 * @param sleepset
	 *            variables of the sleep set
	 */
	void setSleepSet(R state, Map<L, H> sleepset);

	/**
	 * Returns the abstraction level of a reduction state
	 *
	 * @param state
	 *            a state of the reduction automaton
	 * @return the state's abstraction level
	 */
	AbstractionLevel<H> getAbstractionLevel(R state);

	/**
	 * Add additional variables to the abstraction level of a state
	 *
	 * @param state
	 *            a state of the reduction automaton
	 * @param variables
	 *            a set of program variables
	 */
	default void addToAbstractionLevel(final R state, final H variables) {
		getAbstractionLevel(state).addToAbstractionLevel(variables);
	}

	/**
	 * Set a state's abstraction level as defined
	 *
	 * @param state
	 *            whose abstraction level is declared as fully define
	 */
	default void defineAbstractionLevel(final R state) {
		getAbstractionLevel(state).lock();
	}

	/**
	 * Returns the abstraction limit of a reduction state (is the upper limit for the abstraction level of all reduction
	 * states reachable from state)
	 *
	 * @param state
	 *            a state of the reduction automaton
	 * @return the state's abstraction limit
	 */
	AbstractionLevel<H> getAbstractionLimit(R state);

	/**
	 * Add additional variables to the abstraction limit of a state
	 *
	 * @param state
	 *            a state of the reduction automaton
	 * @param variables
	 *            a set of program variables
	 */
	default void addToAbstractionLimit(final R state, final H variables) {
		getAbstractionLimit(state).addToAbstractionLevel(variables);
	}

	/**
	 * If we encounter a loop we need the states inside to be of equal abstraction level. For this reason we need to
	 * create new states that are copies of the states inside the loop with different abstraction levels and limits.
	 * Such states are called loop copies.
	 *
	 * @param state
	 *            state of the reduction automaton
	 * @return true if the state is a loop copy state
	 */
	default boolean isLoopCopy(final R state) {
		return getAbstractionLimit(state).isLocked();
	}

	/**
	 * Return true if the state is a loop entry node
	 *
	 * @param state
	 *            the state in question
	 * @return true state is a loop entry node
	 */
	boolean isLoopNode(final R state);

	/**
	 * Indicate that a state is a loop entry node, i.e. part of a loop and the first state of the loop reached by the
	 * traversal
	 *
	 * @param state
	 *            state to be marked as loop entry node
	 */
	void setAsLoopNode(final R state);

	/**
	 * Only relevant for loop entry nodes
	 *
	 * @param state
	 *            state of the reduction automaton
	 * @return abstraction level we guessed the loop to have
	 *
	 */
	H guessedLevel(final R state);

	/**
	 * Guess a new abstraction level for a loop entry node
	 *
	 * @param state
	 *            state of the reduction automaton, should be a loop entry node
	 */
	void setGuessedLevel(R state, H guess);
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
 * @param <H>
 *            Type representing the value of an abstraction level
 */

class StratifiedStateFactory<L, S, H> implements IStratifiedStateFactory<L, S, StratifiedReductionState<L, S, H>, H> {

	// Wir wollen nicht wirklich einen Kellerautomaten
	@Override
	public StratifiedReductionState<L, S, H> createEmptyStackState() {
		throw new UnsupportedOperationException();
	}

	@Override
	public StratifiedReductionState<L, S, H> createStratifiedState(final S state, final AbstractionLevel<H> level,
			final AbstractionLevel<H> limit) {
		return new StratifiedReductionState<>(state, level, limit);
	}

	@Override
	public S getOriginalState(final StratifiedReductionState<L, S, H> state) {
		return state.mOriginalState;
	}

	@Override
	public Map<L, H> getSleepSet(final StratifiedReductionState<L, S, H> state) {
		return state.mSleepSet;
	}

	@Override
	public AbstractionLevel<H> getAbstractionLevel(final StratifiedReductionState<L, S, H> state) {
		return state.mAbstractionLevel;
	}

	@Override
	public AbstractionLevel<H> getAbstractionLimit(final StratifiedReductionState<L, S, H> state) {
		return state.mAbstractionLimit;
	}

	@Override
	public void setSleepSet(final StratifiedReductionState<L, S, H> state, final Map<L, H> sleepset) {
		state.mSleepSet = sleepset;
	}

	@Override
	public boolean isLoopNode(final StratifiedReductionState<L, S, H> state) {
		return state.mLoopNode;
	}

	@Override
	public void setAsLoopNode(final StratifiedReductionState<L, S, H> state) {
		state.mLoopNode = true;
	}

	@Override
	public H guessedLevel(final StratifiedReductionState<L, S, H> state) {
		return state.mGuessedLevel;
	}

	@Override
	public void setGuessedLevel(final StratifiedReductionState<L, S, H> state, final H guess) {
		state.mGuessedLevel = guess;
	}
}

/**
 * Create a state of the reduction automaton for dynamic stratified reduction
 *
 * @param originalState
 *            state of the input automaton
 * @param sleepSet
 *            a map letter -> abstraction level
 * @param abstractionLevel
 *            an object with a set of program variables 'value' and a boolean 'locked' locked = true means that the
 *            abstraction level is fully defined and no more variables will be added to its value
 * @param abstractionLimit
 *            an object with a set of program variables 'value' and a boolean 'locked' locked = true means that the
 *            state with this abstraction limit is part of a loop copy with this abstraction limit <-- not anymore
 *
 * @return the corresponding state of the reduction automaton
 */

class StratifiedReductionState<L, S, H> {
	protected final S mOriginalState;
	protected Map<L, H> mSleepSet;
	protected final AbstractionLevel<H> mAbstractionLevel;
	protected final AbstractionLevel<H> mAbstractionLimit;
	protected boolean mLoopNode;
	protected H mGuessedLevel;

	public StratifiedReductionState(final S state, final AbstractionLevel<H> absLv, final AbstractionLevel<H> absLmt) {
		mOriginalState = state;
		mAbstractionLevel = absLv;
		mAbstractionLimit = absLmt;
		mLoopNode = false;
	}
}
