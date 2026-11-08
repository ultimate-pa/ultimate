/*
 * Copyright (C) 2026 University of Freiburg
 * Copyright (C) 2026 LMU Munich
 * Copyright (C) 2026 Max Barth (Max.Barth@lmu.de)
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
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
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
package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.parallel.valueanalysis;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;
import java.util.function.BooleanSupplier;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure.IIcfgTransition;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteConfiguration;
import de.uni_freiburg.informatik.ultimate.lib.valueanalysis.ConcreteNwaSemantics;

/**
 * Explores the concrete configurations breadth-first, so the first violation it finds has a shortest run. It never
 * visits a configuration twice and stops when it visited as many as its budget allows.
 *
 * @param <L>
 *            the type of letters
 * @author Max Barth (max.barth@lmu.de)
 */
public final class BreadthFirstConcreteSearch<L extends IIcfgTransition<?>> implements IConcreteSearchStrategy<L> {
	// Polling keepGoing asks the progress monitor, which is cheap but not free.
	private static final int POLL_INTERVAL = 64;

	private int mVisited;
	private int mExpanded;
	private int mErrorsFound;
	private int mMaxLength;
	private String mOutcome = "not run";

	@Override
	public ConcreteConfiguration<L> search(final ConcreteNwaSemantics<L> semantics, final BooleanSupplier keepGoing,
			final Predicate<ConcreteConfiguration<L>> confirm) {
		// Stays if something is thrown out of the search, e.g. by a cancelled confirmation.
		mOutcome = "aborted";
		final Set<ConcreteConfiguration<L>> visited = new HashSet<>();
		final Queue<ConcreteConfiguration<L>> queue = new ArrayDeque<>();
		for (final ConcreteConfiguration<L> initial : semantics.initialConfigurations()) {
			if (visited.add(initial)) {
				queue.add(initial);
			}
		}
		mVisited = visited.size();
		while (!queue.isEmpty()) {
			if (mExpanded % POLL_INTERVAL == 0 && !keepGoing.getAsBoolean()) {
				mOutcome = "stopped";
				return null;
			}
			final ConcreteConfiguration<L> current = queue.poll();
			mExpanded++;
			for (final ConcreteConfiguration<L> successor : semantics.successors(current)) {
				if (!visited.add(successor)) {
					continue;
				}
				mVisited = visited.size();
				mMaxLength = Math.max(mMaxLength, successor.getLength());
				if (semantics.isError(successor)) {
					mErrorsFound++;
					if (confirm.test(successor)) {
						mOutcome = "found a violation";
						return successor;
					}
					// An error location has no successors worth exploring.
					continue;
				}
				queue.add(successor);
			}
		}
		// Not a proof of safety: the values tried for nondeterministic choices are only a few.
		mOutcome = "explored every configuration reachable with the tried values";
		return null;
	}

	@Override
	public String getStatistics() {
		return String.format("BFS %s: %d configurations visited, %d expanded, %d error configurations found, longest "
				+ "run %d letters", mOutcome, mVisited, mExpanded, mErrorsFound, mMaxLength);
	}
}
