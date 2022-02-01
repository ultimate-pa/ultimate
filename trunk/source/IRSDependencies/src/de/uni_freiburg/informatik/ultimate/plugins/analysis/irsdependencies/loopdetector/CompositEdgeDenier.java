/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE IRSDependencies plug-in.
 * 
 * The ULTIMATE IRSDependencies plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE IRSDependencies plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IRSDependencies plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IRSDependencies plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE IRSDependencies plug-in grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Iterator;
import java.util.List;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
public final class CompositEdgeDenier<E> implements IEdgeDenier<E> {

	private final List<IEdgeDenier<E>> mEdgeDeniers;

	public CompositEdgeDenier(Collection<IEdgeDenier<E>> edgeDenier) {
		if (edgeDenier != null) {
			mEdgeDeniers = new ArrayList<IEdgeDenier<E>>(edgeDenier.size());
			for (final IEdgeDenier<E> denier : edgeDenier) {
				mEdgeDeniers.add(denier);
			}
		} else {
			mEdgeDeniers = Collections.emptyList();
		}
	}

	@Override
	public boolean isForbidden(E edge, Iterator<E> currentTrace) {
		final CachedIterator<E> cachedIter = new CachedIterator<>(currentTrace);
		for (final IEdgeDenier<E> denier : mEdgeDeniers) {
			if (denier.isForbidden(edge, cachedIter)) {
				return true;
			}
			cachedIter.reset();
		}
		return false;
	}

	private static final class CachedIterator<E> implements Iterator<E> {

		private Iterator<E> mIter;
		private final List<E> mCache;
		private boolean mComplete;
		private boolean mUsed;

		private CachedIterator(Iterator<E> iter) {
			mIter = iter;
			mUsed = false;
			mComplete = false;
			mCache = new ArrayList<>();
		}

		@Override
		public boolean hasNext() {
			final boolean rtr = mIter.hasNext();
			if (!mComplete && !rtr) {
				mComplete = true;
			}
			return rtr;
		}

		@Override
		public E next() {
			mUsed = true;
			final E rtr = mIter.next();
			if (!mComplete) {
				mCache.add(rtr);
			}
			return rtr;
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException("remove");
		}

		public void reset() {
			if (!mUsed) {
				return;
			}
			while (hasNext()) {
				next();
			}
			mIter = mCache.iterator();
			mUsed = false;
		}
	}
}
