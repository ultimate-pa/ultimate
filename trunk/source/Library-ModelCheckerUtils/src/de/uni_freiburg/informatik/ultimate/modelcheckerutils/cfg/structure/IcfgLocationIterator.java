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
import java.util.Deque;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.Spliterator;
import java.util.Spliterators;
import java.util.stream.Stream;
import java.util.stream.StreamSupport;

/**
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public class IcfgLocationIterator<LOC extends IcfgLocation> implements Iterator<LOC> {
	
	private final Deque<LOC> mWorklist;
	private final Set<LOC> mFinished;
	
	public IcfgLocationIterator(final LOC location) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.add(location);
	}
	
	public IcfgLocationIterator(final Collection<LOC> locations) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.addAll(locations);
	}
	
	public IcfgLocationIterator(final IIcfg<LOC> icfg) {
		mFinished = new HashSet<>();
		mWorklist = new ArrayDeque<>();
		mWorklist.addAll(icfg.getInitialNodes());
	}
	
	@Override
	public boolean hasNext() {
		return !mWorklist.isEmpty();
	}
	
	@Override
	public LOC next() {
		final LOC current = mWorklist.removeFirst();
		current.getOutgoingEdges().stream().map(a -> (LOC) a.getTarget()).filter(mFinished::add)
				.forEachOrdered(mWorklist::add);
		return current;
	}
	
	public Stream<LOC> asStream() {
		return StreamSupport.stream(Spliterators.spliteratorUnknownSize(this, Spliterator.ORDERED), false);
	}
}
