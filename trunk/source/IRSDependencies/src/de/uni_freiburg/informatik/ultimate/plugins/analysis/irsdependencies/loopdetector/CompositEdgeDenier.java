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
			for (IEdgeDenier<E> denier : edgeDenier) {
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
		private List<E> mCache;
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