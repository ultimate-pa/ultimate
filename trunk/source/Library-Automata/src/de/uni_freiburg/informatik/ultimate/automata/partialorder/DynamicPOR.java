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

import java.util.Comparator;
import java.util.Set;
import java.util.stream.Collectors;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.UnfoldToTree.IUnfoldStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.DynamicPORVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;

/**
 * A facade for the use of dynamic partial order reduction (DPOR). Use this class instead of creating a
 * {@link DynamicPORVisitor} directly.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class DynamicPOR {
	private DynamicPOR() {
	}

	// TODO Are we sure this is sound?
	public static <L, S, U> void applyWithoutSleepSets(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IIndependenceRelation<?, L> independence,
			final IDfsOrder<L, S> dfsOrder, final IUnfoldStateFactory<L, S, U> stateFactory,
			final IDfsVisitor<L, U> visitor, final IDisabling<L> disabling, final IMembranes<L, U> membrane,
			final IEnabling<L, U> enabling) throws AutomataOperationCanceledException {
		final var unfolded = new UnfoldToTree<>(services, operand, stateFactory);
		final var liftedOrder = new LiftedDfsOrder<>(dfsOrder, stateFactory);
		final var combinedVisitor = new DynamicPORVisitor<>(visitor, unfolded, liftedOrder, independence, disabling,
				new FilteredMembranes<>(membrane, unfolded), enabling);
		DepthFirstTraversal.traverse(services, unfolded, liftedOrder, combinedVisitor);
	}

	public static <L, S, U, R> void applyWithSleepSets(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IIndependenceRelation<S, L> independence,
			final IDfsOrder<L, R> dfsOrder, final ISleepSetStateFactory<L, S, R> sleepSetStateFactory,
			final IUnfoldStateFactory<L, R, U> unfoldStateFactory, final IDfsVisitor<L, U> visitor,
			final IDisabling<L> disabling, final IMembranes<L, U> membrane, final IEnabling<L, U> enabling)
			throws AutomataOperationCanceledException {
		final var sleepSetReduction =
				new MinimalSleepSetReduction<>(operand, sleepSetStateFactory, independence, dfsOrder);
		applyWithoutSleepSets(services, sleepSetReduction, independence, dfsOrder, unfoldStateFactory, visitor,
				disabling, membrane, enabling);
	}

	private static class FilteredMembranes<L, S> implements IMembranes<L, S> {
		private final IMembranes<L, S> mUnderlying;
		private final INwaOutgoingLetterAndTransitionProvider<L, S> mOperand;

		public FilteredMembranes(final IMembranes<L, S> underlying,
				final INwaOutgoingLetterAndTransitionProvider<L, S> operand) {
			mUnderlying = underlying;
			mOperand = operand;
		}

		@Override
		public Set<L> getMembraneSet(final S s) {
			return mUnderlying.getMembraneSet(s).stream()
					.filter(x -> mOperand.internalSuccessors(s, x).iterator().hasNext()).collect(Collectors.toSet());
		}
	}

	private static class LiftedDfsOrder<L, S, U> implements IDfsOrder<L, U> {
		private final IDfsOrder<L, S> mUnderlying;
		private final IUnfoldStateFactory<L, S, U> mStateFactory;

		public LiftedDfsOrder(final IDfsOrder<L, S> underlying, final IUnfoldStateFactory<L, S, U> stateFactory) {
			mUnderlying = underlying;
			mStateFactory = stateFactory;
		}

		@Override
		public Comparator<L> getOrder(final U treeNode) {
			return mUnderlying.getOrder(mStateFactory.getCurrentState(treeNode));
		}

		@Override
		public boolean isPositional() {
			return mUnderlying.isPositional();
		}
	}
}
