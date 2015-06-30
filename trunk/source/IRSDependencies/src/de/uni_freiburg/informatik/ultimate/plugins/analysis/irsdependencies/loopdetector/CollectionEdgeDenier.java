package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Collection;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

final class CollectionEdgeDenier<E> implements IEdgeDenier<E> {

	private final Set<E> mForbiddenEdges;

	CollectionEdgeDenier(Collection<E> edges) {
		mForbiddenEdges = new HashSet<>(edges);
	}

	@Override
	public boolean isForbidden(E edge, Iterator<E> currentTrace) {
		return mForbiddenEdges.contains(edge);
	}
}