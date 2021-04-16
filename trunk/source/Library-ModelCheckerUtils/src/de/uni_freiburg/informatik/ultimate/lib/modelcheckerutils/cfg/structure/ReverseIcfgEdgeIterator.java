/*
 * Copyright (C) 2021 Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Copyright (C) 2021 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.structure;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.function.Predicate;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 * Variation of {@link IcfgEdgeIterator} that goes backwards.
 *
 * @author Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 */
public class ReverseIcfgEdgeIterator implements Iterator<IcfgEdge> {
	private final Deque<IcfgEdge> mWorklist = new ArrayDeque<>();
	private final Set<IcfgEdge> mFinished = new HashSet<>();
	private final Predicate<IcfgEdge> mIncludePredecessors;

	/**
	 * Create a new iterator
	 *
	 * @param <T>
	 *            a sub-type of {@link IcfgEdge}
	 * @param startEdges
	 *            A set of edges that serve as start-point
	 * @param includePredecessors
	 *            an optional predicate that determines if a given edge's predecessors are iterated over or not (null if
	 *            no predicate should be used, and predecessors are always included)
	 */
	public <T extends IcfgEdge> ReverseIcfgEdgeIterator(final Collection<T> startEdges,
			final Predicate<IcfgEdge> includePredecessors) {
		mWorklist.addAll(startEdges);
		mIncludePredecessors = includePredecessors;
	}

	@Override
	public boolean hasNext() {
		return !mWorklist.isEmpty();
	}

	@Override
	public IcfgEdge next() {
		final IcfgEdge current = mWorklist.removeFirst();
		final IcfgLocation source = current.getSource();
		if (source != null && (mIncludePredecessors == null || mIncludePredecessors.test(current))) {
			source.getIncomingEdges().stream().filter(mFinished::add).forEachOrdered(mWorklist::add);
		}
		assert source != null : "Dangling edge";
		return current;
	}

	/**
	 * Creates a stream from the iterator.
	 */
	public Stream<IcfgEdge> asStream() {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(this, Spliterator.ORDERED), false);
	}
}