package de.uni_freiburg.informatik.ultimate.plugins.analysis.irsdependencies.loopdetector;

import java.util.Map;
import java.util.Map.Entry;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
class OpenItem<V, E> {
	private V mNode;
	private ScopedHashMap<V, AstarAnnotation<E>> mAnnotations;
	private AstarAnnotation<E> mAnnotation;

	public OpenItem(V node, Map<V, AstarAnnotation<E>> annotations) {
		mNode = node;
		mAnnotations = new ScopedHashMap<>();
		for (Entry<V, AstarAnnotation<E>> entry : annotations.entrySet()) {
			mAnnotations.put(entry.getKey(), entry.getValue());
		}
	}

	public OpenItem(V node, OpenItem<V, E> current) {
		mNode = node;
		mAnnotations = new ScopedHashMap<>(current.mAnnotations);
	}

	public V getNode() {
		return mNode;
	}

	public ScopedHashMap<V, AstarAnnotation<E>> getAnnotations() {
		return mAnnotations;
	}

	public AstarAnnotation<E> getAnnotation() {
		if (mAnnotation == null) {
			mAnnotation = mAnnotations.get(mNode);
		}
		return mAnnotation;
	}

	@Override
	public int hashCode() {
		return getAnnotation().hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj == null) {
			return false;
		}
		if (!obj.getClass().equals(getClass())) {
			return false;
		}
		final OpenItem<?, ?> other = (OpenItem<?, ?>) obj;
		return other.getAnnotation().equals(getAnnotation());
	}
}
