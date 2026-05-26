/*
 * Copyright (C) 2026 Matthias Zumkeller
 * Copyright (C) 2026 University of Freiburg
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
import java.util.function.Function;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.visitors.WrapperVisitor;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IAction;
import de.uni_freiburg.informatik.ultimate.lib.tracecheckerutils.partialorder.IDPMainOrder.IDPMainComparator;

public class IDPIsrOrder<L extends IAction, S> implements IDfsOrder<L, S> {

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);
	private final Map<Object, L> mEntryEdge = new HashMap<>();
	private final Function<S, Object> mNormalizer;

	public IDPIsrOrder() {
		this(null);
	}

	public IDPIsrOrder(final Function<S, Object> normalizer) {
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

		return new IDPMainComparator<>(mDefaultComparator);
	}

	@Override
	public boolean isPositional() {
		return true;
	}

	public <V extends IDfsVisitor<L, S>> WrapperVisitor<L, S, V> wrapVisitor(final V underlying) {
		return new Visitor<>(underlying);
	}

	private Object normalize(final S state) {
		if (mNormalizer == null) {
			return state;
		}
		return mNormalizer.apply(state);
	}

	public static final class IDPIsrComparator<L extends IAction> implements Comparator<L> {
		private static String MAIN_THREAD = "ULTIMATE.start";
		private final Comparator<L> mFallback;

		public IDPIsrComparator(final Comparator<L> fallback) {
			mFallback = fallback;
		}

		@Override
		public int compare(final L x, final L y) {
			final String xThread = x.getPrecedingProcedure();
			final var xMainThread = xThread.equals(MAIN_THREAD);
			final String yThread = y.getPrecedingProcedure();
			final var yMainThread = yThread.equals(MAIN_THREAD);
			if (xMainThread && !yMainThread) {
				return -1;
			}

			if (!xMainThread && yMainThread) {
				return 1;
			}
			return mFallback.compare(x, y);
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
