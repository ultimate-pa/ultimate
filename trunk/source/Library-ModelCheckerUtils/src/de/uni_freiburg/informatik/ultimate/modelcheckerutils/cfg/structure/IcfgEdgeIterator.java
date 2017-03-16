/*
 * Copyright (C) 2016 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.structure;

import java.util.ArrayDeque;
import java.util.Collection;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgEdgeIterator implements Iterator<IcfgEdge> {

	private final Deque<IcfgEdge> mWorklist;
	private final Set<IcfgEdge> mFinished;

	public <T extends IcfgEdge> IcfgEdgeIterator(final T edge) {
		this(Collections.singleton(edge));
	}

	public <T extends IcfgEdge> IcfgEdgeIterator(final Collection<T> edges) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.addAll(edges);
		mFinished.addAll(mWorklist);
	}

	public IcfgEdgeIterator(final IIcfg<?> icfg) {
		this(icfg.getInitialNodes().stream().flatMap(a -> a.getOutgoingEdges().stream()).collect(Collectors.toSet()));
	}

	@Override
	public boolean hasNext() {
		return !mWorklist.isEmpty();
	}

	@Override
	public IcfgEdge next() {
		final IcfgEdge current = mWorklist.removeFirst();
		final IcfgLocation target = current.getTarget();
		if (target == null) {
			assert false : "Dangling edge";
			return current;
		}
		target.getOutgoingEdges().stream().filter(mFinished::add).forEachOrdered(mWorklist::add);
		return current;
	}

	public Stream<IcfgEdge> asStream() {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(this, Spliterator.ORDERED), false);
	}
}
