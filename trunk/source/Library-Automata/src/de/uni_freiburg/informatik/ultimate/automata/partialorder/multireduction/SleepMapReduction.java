/*
 * Copyright (C) 2022 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2022 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction;

import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;

/**
 * Implementation of sleep map reduction: A kind of partial order reduction up to multiple independence relations.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters
 * @param <S>
 *            The type of states in the input automaton
 * @param <R>
 *            The type of states in the reduction automaton
 */
public class SleepMapReduction<L, S, R> implements INwaOutgoingLetterAndTransitionProvider<L, R> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IDfsOrder<L, R> mOrder;
	private final List<IIndependenceRelation<S, L>> mRelations;
	private final ISleepMapStateFactory<L, S, R> mStateFactory;
	private final IBudgetFunction<L, R> mBudgetFunction;

	private final R mInitial;

	/**
	 * Create a new reduction automaton.
	 *
	 * @param operand
	 *            The input automaton
	 * @param relations
	 *            An ordered sequence of independence relations. The {@code operand} must be closed up to each of these
	 *            relations.
	 * @param order
	 *            The preference order for the reduction
	 * @param stateFactory
	 *            A state factory to create the reduction automaton's states
	 * @param getBudget
	 *            A budget function that determines how the different independence relations are combined
	 */
	public SleepMapReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final List<IIndependenceRelation<S, L>> relations, final IDfsOrder<L, R> order,
			final ISleepMapStateFactory<L, S, R> stateFactory,
			final Function<SleepMapReduction<L, S, R>, IBudgetFunction<L, R>> getBudget) {
		mOperand = operand;
		mOrder = order;
		mRelations = relations;
		mStateFactory = stateFactory;

		final var oldInitial =
				DataStructureUtils.getOnly(operand.getInitialStates(), "There must only be one initial state");
		if (oldInitial.isPresent()) {
			mInitial = mStateFactory.createSleepMapState(oldInitial.get(), SleepMap.empty(mRelations), maximumBudget());
		} else {
			mInitial = null;
		}

		mBudgetFunction = getBudget.apply(this);
	}

	@Override
	public IStateFactory<R> getStateFactory() {
		return mStateFactory;
	}

	@Override
	public VpAlphabet<L> getVpAlphabet() {
		return mOperand.getVpAlphabet();
	}

	@Override
	public R getEmptyStackState() {
		return mStateFactory.createEmptyStackState();
	}

	@Override
	public Iterable<R> getInitialStates() {
		return mInitial == null ? Collections.emptySet() : Set.of(mInitial);
	}

	@Override
	public boolean isInitial(final R state) {
		return Objects.equals(mInitial, state);
	}

	@Override
	public boolean isFinal(final R state) {
		return mOperand.isFinal(mStateFactory.getOriginalState(state));
	}

	@Override
	public int size() {
		return -1;
	}

	@Override
	public String sizeInformation() {
		return "[size unknown]";
	}

	@Override
	public Set<L> lettersInternal(final R state) {
		return mOperand.lettersInternal(mStateFactory.getOriginalState(state)).stream().sorted(mOrder.getOrder(state))
				.filter(x -> !isPruned(state, x)).collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, R>> internalSuccessors(final R state, final L letter) {
		if (isPruned(state, letter)) {
			return Collections.emptySet();
		}
		final R successor = computeSuccessorWithBudget(state, letter, mBudgetFunction.computeBudget(state, letter));
		if (successor == null) {
			return Collections.emptySet();
		}
		return Set.of(new OutgoingInternalTransition<>(letter, successor));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, R>> callSuccessors(final R state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, R>> returnSuccessors(final R state, final R hier, final L letter) {
		return Collections.emptySet();
	}

	/**
	 * Compute a successor state under the assumption of some given budget.
	 *
	 * @param state
	 *            The current state of the reduction automaton
	 * @param letter
	 *            The input letter, for which the successor state shall be computed
	 * @param budget
	 *            The assumed budget given to the successor state
	 * @return The successor state for the given state and letter, assuming the budget function assigns the given budget
	 */
	R computeSuccessorWithBudget(final R state, final L letter, final int budget) {
		final S currentState = mStateFactory.getOriginalState(state);
		final var currentTransitionOpt = DataStructureUtils.getOnly(mOperand.internalSuccessors(currentState, letter),
				"Automaton must be deterministic");
		if (currentTransitionOpt.isEmpty()) {
			return null;
		}

		final SleepMap<L, S> currentSleepMap = mStateFactory.getSleepMap(state);
		final Comparator<L> comp = mOrder.getOrder(state);

		final Map<L, Integer> explored = mOperand.lettersInternal(currentState).stream()
				.filter(b -> comp.compare(b, letter) < 0 && !isPruned(state, b))
				.collect(Collectors.toMap(Function.identity(), b -> mBudgetFunction.computeBudget(state, b)));
		final SleepMap<L, S> succSleepMap = currentSleepMap.computeSuccessor(currentState, letter, explored, budget);
		return mStateFactory.createSleepMapState(currentTransitionOpt.get().getSucc(), succSleepMap, budget);
	}

	private int maximumBudget() {
		return mRelations.size() - 1;
	}

	private boolean isPruned(final R state, final L letter) {
		final SleepMap<L, S> sleepMap = mStateFactory.getSleepMap(state);
		if (!sleepMap.contains(letter)) {
			return false;
		}
		final int oldCost = sleepMap.getPrice(letter);
		final int newCost = mBudgetFunction.computeBudget(state, letter);
		assert newCost <= mStateFactory.getBudget(state) : "Budget limit exceeded";
		return oldCost <= newCost;
	}

	/**
	 * A budget function determines how the different independence relation shall be combined.
	 *
	 * Specifically, it assigns a number <code>k</code> from <code>0</code> to <code>n-1</code> (where n is the number
	 * of independence relations) to a state. In this state, and all states reachable from it, the reduction may then
	 * only apply the independence relations at indices from 0 to k in the sequence of independence relations.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the reduction automaton
	 * @param <R>
	 *            The type of reduction automaton states
	 */
	public interface IBudgetFunction<L, R> {
		/**
		 * Given a state and an input letter, assigns the budget for the successor state.
		 *
		 * The assigned budget must always be between 0 and the given state's budget (inclusive), it may never exceed
		 * the given state's budget.
		 *
		 * @param state
		 *            The current state of the reduction automaton. An {@link ISleepMapStateFactory} may be used to
		 *            decompose it.
		 * @param letter
		 *            An input letter
		 * @return The budget for the successor state of <code>state</code> under input <code>letter</code>
		 */
		int computeBudget(R state, L letter);
	}
}
