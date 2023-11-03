/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
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
import java.util.Objects;
import java.util.Set;
import java.util.stream.Stream;

import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.NestedWordAutomataUtils;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.VpAlphabet;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingCallTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingInternalTransition;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.transitions.OutgoingReturnTransition;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation.Dependence;
import de.uni_freiburg.informatik.ultimate.automata.statefactory.IStateFactory;
import de.uni_freiburg.informatik.ultimate.util.datastructures.DataStructureUtils;
import de.uni_freiburg.informatik.ultimate.util.datastructures.ImmutableSet;

/**
 * Implementation of the Sleep Set Reduction with new states. The reduction automaton partially unfolds and unrolls the
 * input automaton, in order to guarantee a reduction that is minimal (in terms of the accepted language).
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters of the input automaton.
 * @param <S>
 *            The type of states of the input automaton.
 * @param <R>
 *            The type of states of the reduced automaton.
 */
public class MinimalSleepSetReduction<L, S, R> implements INwaOutgoingLetterAndTransitionProvider<L, R> {
	private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;
	private final ISleepSetStateFactory<L, S, R> mStateFactory;
	private final IDfsOrder<L, R> mOrder;
	private final IIndependenceRelation<S, L> mIndependence;

	private final R mInitial;

	/**
	 * Create a new reduction automaton.
	 *
	 * @param operand
	 *            The input automaton
	 * @param stateFactory
	 *            A state factory to create the reduction automaton's states
	 * @param independenceRelation
	 *            The independence relation up to which a reduction is computed. The input automaton must be closed up
	 *            to this independence relation.
	 * @param order
	 *            The preference order for the reduction
	 */
	public MinimalSleepSetReduction(final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final ISleepSetStateFactory<L, S, R> stateFactory, final IIndependenceRelation<S, L> independenceRelation,
			final IDfsOrder<L, R> order) {
		assert NestedWordAutomataUtils.isFiniteAutomaton(operand) : "Sleep sets support only finite automata";

		mOperand = operand;
		mStateFactory = stateFactory;
		mOrder = order;
		mIndependence = independenceRelation;

		final var initial =
				DataStructureUtils.getOnly(operand.getInitialStates(), "There must only be one initial state");
		if (initial.isPresent()) {
			mInitial = mStateFactory.createSleepSetState(initial.get(), ImmutableSet.empty());
		} else {
			mInitial = null;
		}
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
		return "currently " + size() + " states, but on-demand construction may add more states";
	}

	@Override
	public Set<L> lettersInternal(final R state) {
		return DataStructureUtils.difference(mOperand.lettersInternal(mStateFactory.getOriginalState(state)),
				mStateFactory.getSleepSet(state));
	}

	@Override
	public Iterable<OutgoingInternalTransition<L, R>> internalSuccessors(final R state, final L letter) {
		final ImmutableSet<L> currentSleepSet = mStateFactory.getSleepSet(state);
		if (currentSleepSet.contains(letter)) {
			return Collections.emptySet();
		}

		final S currentState = mStateFactory.getOriginalState(state);
		final var currentTransitionOpt = DataStructureUtils.getOnly(mOperand.internalSuccessors(currentState, letter),
				"Automaton must be deterministic");
		if (currentTransitionOpt.isEmpty()) {
			return Collections.emptySet();
		}

		final Comparator<L> comp = mOrder.getOrder(state);
		final Stream<L> explored = mOperand.lettersInternal(currentState).stream()
				.filter(x -> comp.compare(x, letter) < 0 && !currentSleepSet.contains(x));

		// TODO factor out sleep set successor computation
		final ImmutableSet<L> succSleepSet =
				ImmutableSet.of((Set<L>) Set.of(Stream.concat(currentSleepSet.stream(), explored)
						.filter(l -> mIndependence.isIndependent(currentState, letter, l) == Dependence.INDEPENDENT)
						.toArray()));

		final R succSleepSetState =
				mStateFactory.createSleepSetState(currentTransitionOpt.get().getSucc(), succSleepSet);
		return Set.of(new OutgoingInternalTransition<>(letter, succSleepSetState));
	}

	@Override
	public Iterable<OutgoingCallTransition<L, R>> callSuccessors(final R state, final L letter) {
		return Collections.emptySet();
	}

	@Override
	public Iterable<OutgoingReturnTransition<L, R>> returnSuccessors(final R state, final R hier, final L letter) {
		return Collections.emptySet();
	}
}
