/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceCheckerUtils Library.
 *
 * The ULTIMATE TraceCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;

/**
 * Approximates lockstep (round robin) order by recording for each state the first discovered edge through which the
 * state is reached, and hence its thread. From this the next thread to be scheduled is determined.
 *
 * In order to record the edge, a wrapper DFS visitor is employed. This order only works if this visitor is used.
 *
 * May deviate from precise lockstep (round robin) if and ONLY if the same state is reached through multiple paths.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 *
 * @param <L>
 *            The type of letters in the automaton. {@link IAction#getPrecedingProcedure()} is used to determine the
 *            thread to which a letter belongs.
 * @param <S>
 *            The type of states in the automaton.
 */
public class BetterLockstepOrder<L extends IAction, S> implements IDfsOrder<L, S> {
	private final Map<Object, L> mEntryEdge = new HashMap<>();
	private final Function<S, Object> mNormalizer;

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	/**
	 * Creates a new lockstep order.
	 */
	public BetterLockstepOrder() {
		this(null);
	}

	/**
	 * Creates a new lockstep order.
	 *
	 * @param normalizer
	 *            A normalizing function: States normalized to the same object will be assigned the same order.
	 */
	public BetterLockstepOrder(final Function<S, Object> normalizer) {
		mNormalizer = normalizer;
	}

	@Override
	public Comparator<L> getOrder(final S state) {
		final Object key = normalize(state);
		final L entryEdge = mEntryEdge.get(key);

		if (entryEdge == null) {
			// should only happen for the initial state
			return mDefaultComparator;
		}

		final String lastThread = entryEdge.getPrecedingProcedure();
		return new RoundRobinComparator<>(lastThread, mDefaultComparator);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	/**
	 * Creates a visitor that wraps a given visitor and delegates all calls to it. The wrapper visitor is needed for the
	 * round robin order to work.
	 *
	 * @param underlying
	 *            The underlying visitor
	 * @return a newly created wrapper visitor
	 */
	public <V extends IDfsVisitor<L, S>> WrapperVisitor<L, S, V> wrapVisitor(final V underlying) {
		return new Visitor<>(underlying);
	}

	public static final class RoundRobinComparator<L extends IAction> implements Comparator<L> {
		private final String mLastThread;
		private final Comparator<L> mFallback;

		public RoundRobinComparator(final String lastThread, final Comparator<L> fallback) {
			mLastThread = Objects.requireNonNull(lastThread);
			mFallback = fallback;
		}

		@Override
		public int compare(final L x, final L y) {
			final String xThread = x.getPrecedingProcedure();
			final boolean xBefore = mLastThread.compareTo(xThread) >= 0;
			final String yThread = y.getPrecedingProcedure();
			final boolean yBefore = mLastThread.compareTo(yThread) >= 0;
			if (xBefore && !yBefore) {
				return 1;
			}
			if (yBefore && !xBefore) {
				return -1;
			}
			return mFallback.compare(x, y);
		}

		@Override
		public int hashCode() {
			return Objects.hash(mFallback, mLastThread);
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final RoundRobinComparator<L> other = (RoundRobinComparator<L>) obj;
			return Objects.equals(mFallback, other.mFallback) && Objects.equals(mLastThread, other.mLastThread);
		}
	}

	private final class Visitor<V extends IDfsVisitor<L, S>> extends WrapperVisitor<L, S, V> {
		private Visitor(final V underlying) {
			super(underlying);
		}

		@Override
		public boolean discoverTransition(final S source, final L letter, final S target) {
			mEntryEdge.putIfAbsent(normalize(target), letter);
			return super.discoverTransition(source, letter, target);
		}
	}
}
