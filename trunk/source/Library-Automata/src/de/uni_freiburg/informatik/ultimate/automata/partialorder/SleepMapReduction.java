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
package de.uni_freiburg.informatik.ultimate.automata.partialorder;

import java.util.Collections;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiFunction;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

public class SleepMapReduction<L, S, R> implements INwaOutgoingLetterAndTransitionProvider<L, R> {

	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final IDfsOrder<L, R> mOrder;
	private final List<IIndependenceRelation<S, L>> mRelations;
	private final ISleepMapStateFactory<L, S, R> mStateFactory;
	private final BiFunction<R, L, Integer> mBudgetFunction;

	private final R mInitial;

	public SleepMapReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final List<IIndependenceRelation<S, L>> relations, final IDfsOrder<L, R> order,
			final ISleepMapStateFactory<L, S, R> stateFactory, final BiFunction<R, L, Integer> budget) {
		mOperand = operand;
		mOrder = order;
		mRelations = relations;
		mStateFactory = stateFactory;
		mBudgetFunction = budget;

		final S oldInitial = DataStructureUtils.getOneAndOnly(operand.getInitialStates(), "initial state");
		mInitial = mStateFactory.createSleepMapState(oldInitial, SleepMap.empty(mRelations), maximumBudget());
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
		return Set.of(mInitial);
	}

	@Override
	public boolean isInitial(final R state) {
		return mInitial.equals(state);
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
		return mOperand.lettersInternal(mStateFactory.getOriginalState(state)).stream().filter(x -> !isPruned(state, x))
				.collect(Collectors.toSet());
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, R>> internalSuccessors(final R state, final L letter) {
		if (isPruned(state, letter)) {
			return Collections.emptySet();
		}

		final S currentState = mStateFactory.getOriginalState(state);
		final var currentTransitionOpt = DataStructureUtils.getOnly(mOperand.internalSuccessors(currentState, letter),
				"Automaton must be deterministic");
		if (currentTransitionOpt.isEmpty()) {
			return Collections.emptySet();
		}

		final SleepMap<L, S> currentSleepMap = mStateFactory.getSleepMap(state);
		final Comparator<L> comp = mOrder.getOrder(state);

		final Map<L, Integer> explored = mOperand.lettersInternal(currentState).stream()
				.filter(b -> comp.compare(b, letter) < 0 && !isPruned(state, b))
				.map(b -> new Pair<>(b, mBudgetFunction.apply(state, b)))
				.collect(Collectors.toMap(Pair::getFirst, Pair::getSecond));
		final SleepMap<L, S> succSleepMap = currentSleepMap.computeSuccessor(currentState, letter, explored);

		final R succSleepMapState = mStateFactory.createSleepMapState(currentTransitionOpt.get().getSucc(),
				succSleepMap, mBudgetFunction.apply(state, letter));
		return Set.of(new OutgoingInternalTransition<>(letter, succSleepMapState));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, R>> callSuccessors(final R state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, R>> returnSuccessors(final R state, final R hier, final L letter) {
		return Collections.emptySet();
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
		final int newCost = mBudgetFunction.apply(state, letter);
		assert newCost <= mStateFactory.getBudget(state) : "Budget limit exceeded";
		return oldCost <= newCost;
	}
}
