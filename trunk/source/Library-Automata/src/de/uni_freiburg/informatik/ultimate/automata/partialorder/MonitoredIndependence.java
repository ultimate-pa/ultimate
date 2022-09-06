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

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BinaryOperator;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.polynomials.PolynomialTermUtils.TriFunction;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Quad;
import de.uni_freiburg.informatik.ultimate.util.statistics.IStatisticsDataProvider;

/**
 * Provides a mechanism for external callers to monitor queries of an independence relation and their results.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters of the independence relation
 * @param <S>
 *            The types of states of the independence relation
 */
public class MonitoredIndependence<L, S> implements IIndependenceRelation<S, L> {
	private final List<Pair<IndependenceMonitor<L, S, ?>, Integer>> mRegistrations = new ArrayList<>();
	private final IIndependenceRelation<S, L> mUnderlying;

	public MonitoredIndependence(final IIndependenceRelation<S, L> underlying) {
		mUnderlying = underlying;
	}

	/**
	 * Register a new monitor for calls to this instance
	 *
	 * @param monitor
	 *            The monitor that will be notified of any future calls to this instance.
	 * @return a unique ID with which this relation will identify itself to the monitor
	 */
	public int register(final IndependenceMonitor<L, S, ?> monitor) {
		final int id = monitor.assignIdentifier();
		mRegistrations.add(new Pair<>(monitor, id));
		return id;
	}

	@Override
	public boolean contains(final S state, final L a, final L b) {
		final S condition = mUnderlying.isConditional() ? state : null;
		final var result = mUnderlying.contains(condition, a, b);

		for (final var registration : mRegistrations) {
			registration.getFirst().report(registration.getSecond(), condition, a, b, result);
		}
		return result;
	}

	@Override
	public boolean isSymmetric() {
		return mUnderlying.isSymmetric();
	}

	@Override
	public boolean isConditional() {
		return mUnderlying.isConditional();
	}

	@Override
	public IStatisticsDataProvider getStatistics() {
		return mUnderlying.getStatistics();
	}

	/**
	 * A monitor that is informed of calls to a {@link MonitoredIndependence}, and incrementally computes some result.
	 *
	 * Monitors operate in a stack-like fashion: Callers can push a new frame onto the stack (with a seed result value).
	 * Upon each query to the monitored relation, the result associated with the top-most stack frame will be updated.
	 * Callers can also pop frames from the stack, and decide to either discard the associated values or include them in
	 * the computation for the next-lower stack frame.
	 *
	 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
	 *
	 * @param <L>
	 *            The type of letters of the monitored independence
	 * @param <S>
	 *            The type of states of the monitored independence
	 * @param <E>
	 *            A type of results that are computed by the monitor, and returned to the caller
	 */
	public static final class IndependenceMonitor<L, S, E> {
		private int mIdCounter;

		private final BinaryOperator<E> mCombinator;
		private final TriFunction<E, Quad<S, L, L, Boolean>, Integer, E> mAggregator;

		private final Deque<E> mStack = new ArrayDeque<>();

		/**
		 * Create a new monitor.
		 *
		 * @param combinator
		 *            A binary operation to combine partial results
		 * @param aggregator
		 *            A function that takes the current result, a quadruple describing a query to an independence
		 *            relation, and the id of the relation that was queried, and returns an updated result
		 */
		public IndependenceMonitor(final BinaryOperator<E> combinator,
				final TriFunction<E, Quad<S, L, L, Boolean>, Integer, E> aggregator) {
			mCombinator = combinator;
			mAggregator = aggregator;
		}

		/**
		 * Create a new monitor.
		 *
		 * @param combinator
		 *            A binary operation to combine partial results
		 * @param grader
		 *            A function that takes a quadruple describing a query to an independence relation, and the id of
		 *            the relation that was queried, and returns a partial result for this query
		 */
		public IndependenceMonitor(final BinaryOperator<E> combinator,
				final BiFunction<Quad<S, L, L, Boolean>, Integer, E> grader) {
			this(combinator, (old, in, id) -> combinator.apply(old, grader.apply(in, id)));
		}

		/**
		 * Push a new frame on the stack
		 *
		 * @param seed
		 *            The initial value for the new stack frame's result
		 */
		public void push(final E seed) {
			mStack.push(seed);
		}

		/**
		 * Get the top stack frame's current result
		 *
		 * @return the result for the top stack frame, as computed so far
		 */
		public E peek() {
			return mStack.peek();
		}

		/**
		 * Pop the top stack frame. Do not use its result for the computation of other stack frames.
		 *
		 * @return the popped frame's result
		 */
		public E popAndDiscard() {
			return mStack.pop();
		}

		/**
		 * Pop the top stack frame. Merge its result into the result of the next-lower stack frame, if there is one.
		 *
		 * @return the popped frame's result
		 */
		public E popAndCombine() {
			final var result = mStack.pop();
			if (!mStack.isEmpty()) {
				final var top = mStack.pop();
				mStack.push(mCombinator.apply(top, result));
			}
			return result;
		}

		private void report(final int id, final S state, final L a, final L b, final boolean result) {
			if (mStack.isEmpty()) {
				return;
			}

			final var top = mStack.pop();
			final var newTop = mAggregator.apply(top, new Quad<>(state, a, b, result), id);
			mStack.push(newTop);
		}

		private int assignIdentifier() {
			return mIdCounter++;
		}
	}
}
