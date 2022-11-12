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

import java.util.Comparator;
import java.util.List;
import java.util.Set;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.AutomataLibraryServices;
import de.uni_freiburg.informatik.ultimate.automata.AutomataOperationCanceledException;
import de.uni_freiburg.informatik.ultimate.automata.nestedword.INwaOutgoingLetterAndTransitionProvider;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.independence.IIndependenceRelation;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.CachedBudget;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.ISleepMapStateFactory;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.multireduction.SleepMapReduction.IBudgetFunction;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;

/**
 * Performs persistent set reduction on top of sleep set reduction. The goal of this is primarily to reduce the size (in
 * number of states) of the reduced automaton, not so much the language. In particular, sleep set reduction with new
 * states already yields a minimal reduction (in terms of the language), hence persistent sets do not achieve any
 * further reduction in this sense. Some further language reduction can possibly be achieved in the delay set case.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public final class PersistentSetReduction {
	private PersistentSetReduction() {
	}

	public static <L, S> void applyWithoutSleepSets(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand, final IDfsOrder<L, S> dfsOrder,
			final IPersistentSetChoice<L, S> persistent, final IDfsVisitor<L, S> visitor)
			throws AutomataOperationCanceledException {
		final IDfsOrder<L, S> combinedOrder = new CompatibleDfsOrder<>(persistent, dfsOrder);
		final IDfsVisitor<L, S> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);
		DepthFirstTraversal.traverse(services, operand, combinedOrder, combinedVisitor);
	}

	public static <L, S, R> void applyNewStateReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final IDfsOrder<L, R> dfsOrder,
			final ISleepSetStateFactory<L, S, R> factory, final IPersistentSetChoice<L, R> persistent,
			final IDfsVisitor<L, R> visitor) throws AutomataOperationCanceledException {
		final IDfsOrder<L, R> combinedOrder = new CompatibleDfsOrder<>(persistent, dfsOrder);
		final IDfsVisitor<L, R> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);
		DepthFirstTraversal.traverse(services,
				new MinimalSleepSetReduction<>(operand, factory, independenceRelation, combinedOrder), combinedOrder,
				combinedVisitor);
	}

	public static <L, S, R> void applySleepMapReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final List<IIndependenceRelation<S, L>> independenceRelations, final IDfsOrder<L, R> dfsOrder,
			final ISleepMapStateFactory<L, S, R> factory,
			final Function<SleepMapReduction<L, S, R>, IBudgetFunction<L, R>> getBudget,
			final IPersistentSetChoice<L, R> persistent, final IDfsVisitor<L, R> visitor)
			throws AutomataOperationCanceledException {
		final IDfsOrder<L, R> combinedOrder = new CompatibleDfsOrder<>(persistent, dfsOrder);
		final IDfsVisitor<L, R> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);

		final var red = new SleepMapReduction<>(operand, independenceRelations, combinedOrder, factory,
				getBudget.andThen(CachedBudget::new));
		DepthFirstTraversal.traverse(services, red, combinedOrder, combinedVisitor);
	}

	public static <L, S> void applyDelaySetReduction(final AutomataLibraryServices services,
			final INwaOutgoingLetterAndTransitionProvider<L, S> operand,
			final IIndependenceRelation<S, L> independenceRelation, final IDfsOrder<L, S> dfsOrder,
			final IPersistentSetChoice<L, S> persistent, final IDfsVisitor<L, S> visitor)
			throws AutomataOperationCanceledException {
		final IDfsOrder<L, S> combinedOrder = new CompatibleDfsOrder<>(persistent, dfsOrder);
		final IDfsVisitor<L, S> combinedVisitor = new PersistentSetVisitor<>(persistent, visitor);
		new SleepSetDelayReduction<>(services, operand, new ISleepSetStateFactory.NoUnrolling<>(), independenceRelation,
				combinedOrder, combinedVisitor);
	}

	/**
	 * A visitor that performs persistent set reduction by pruning transitions, and proxies non-pruned calls to an
	 * underlying visitor implementation.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the reduced automaton
	 * @param <S>
	 *            The type of states in the reduced automaton
	 */
	private static class PersistentSetVisitor<L, S> extends WrapperVisitor<L, S, IDfsVisitor<L, S>> {
		private final IPersistentSetChoice<L, S> mPersistent;

		public PersistentSetVisitor(final IPersistentSetChoice<L, S> persistent, final IDfsVisitor<L, S> underlying) {
			super(underlying);
			mPersistent = persistent;
		}

		@Override
		public boolean discoverTransition(final S source, final L letter, final S target) {
			final Set<L> persistent = mPersistent.persistentSet(source);
			if (persistent != null && !persistent.contains(letter)) {
				return true;
			}
			return super.discoverTransition(source, letter, target);
		}
	}

	/**
	 * A sleep set order that can be used with persistent set reduction.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters in the reduced automaton
	 * @param <S>
	 *            The type of states in the reduced automaton
	 */
	private static class CompatibleDfsOrder<L, S> implements IDfsOrder<L, S> {
		private final IPersistentSetChoice<L, S> mPersistent;
		private final IDfsOrder<L, S> mUnderlying;

		public CompatibleDfsOrder(final IPersistentSetChoice<L, S> persistent, final IDfsOrder<L, S> underlying) {
			mPersistent = persistent;
			mUnderlying = underlying;
		}

		@Override
		public Comparator<L> getOrder(final S state) {
			final Set<L> persistent = mPersistent.persistentSet(state);
			final Comparator<L> comparator = mUnderlying.getOrder(state);
			return (a, b) -> {
				if (persistent != null && persistent.contains(a) && !persistent.contains(b)) {
					if (mPersistent.ensuresCompatibility(mUnderlying) && comparator.compare(a, b) >= 0) {
						throw new IllegalStateException("Guarantee of compatibility failed");
					}
					return -1;
				} else if (persistent != null && persistent.contains(b) && !persistent.contains(a)) {
					if (mPersistent.ensuresCompatibility(mUnderlying) && comparator.compare(a, b) <= 0) {
						throw new IllegalStateException("Guarantee of compatibility failed");
					}
					return 1;
				}
				return comparator.compare(a, b);
			};
		}

		@Override
		public boolean isPositional() {
			return mUnderlying.isPositional() || !mPersistent.ensuresCompatibility(mUnderlying);
		}
	}
}
