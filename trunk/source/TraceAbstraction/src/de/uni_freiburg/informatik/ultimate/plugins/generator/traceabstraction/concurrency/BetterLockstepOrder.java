/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 *
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.concurrency;

import java.util.Comparator;
import java.util.HashMap;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsOrder;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.IDfsVisitor;
import de.uni_freiburg.informatik.ultimate.automata.partialorder.WrapperVisitor;
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
	private final Map<S, L> mEntryEdge = new HashMap<>();

	private final Comparator<L> mDefaultComparator =
			Comparator.comparing(L::getPrecedingProcedure).thenComparingInt(Object::hashCode);

	@Override
	public Comparator<L> getOrder(final S state) {
		final L entryEdge = mEntryEdge.get(state);

		if (entryEdge == null) {
			// should only happen for the initial state
			return mDefaultComparator;
		}

		final String lastThread = entryEdge.getPrecedingProcedure();
		return (x, y) -> {
			final String xThread = x.getPrecedingProcedure();
			final boolean xBefore = lastThread.compareTo(xThread) >= 0;
			final String yThread = y.getPrecedingProcedure();
			final boolean yBefore = lastThread.compareTo(yThread) >= 0;
			if (xBefore && !yBefore) {
				return 1;
			}
			if (yBefore && !xBefore) {
				return -1;
			}
			return mDefaultComparator.compare(x, y);
		};
	}

	public void transferOrder(final S oldState, final S newState) {
		final L oldEdge = mEntryEdge.get(oldState);
		final L newEdge = mEntryEdge.get(newState);
		assert newEdge == null || newEdge == oldEdge : "Must not overwrite recorded order";
		if (oldEdge != null) {
			mEntryEdge.put(newState, oldEdge);
		}
	}

	/**
	 * Gets a visitor that wraps a given visitor and delegates all calls to it. The wrapper visitor is needed for the
	 * round robin order to work.
	 *
	 * @param underlying
	 *            The underlying visitor
	 * @return a newly created wrapper visitor
	 */
	public IDfsVisitor<L, S> getWrapperVisitor(final IDfsVisitor<L, S> underlying) {
		return new Visitor(underlying);
	}

	public class Visitor extends WrapperVisitor<L, S, IDfsVisitor<L, S>> {
		private Visitor(final IDfsVisitor<L, S> underlying) {
			super(underlying);
		}

		@Override
		public boolean discoverTransition(final S source, final L letter, final S target) {
			mEntryEdge.putIfAbsent(target, letter);
			return super.discoverTransition(source, letter, target);
		}
	}
}
