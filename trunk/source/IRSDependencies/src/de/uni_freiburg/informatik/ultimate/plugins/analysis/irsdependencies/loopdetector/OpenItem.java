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

import java.util.Map;
import java.util.Map.Entry;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 *
 */
class OpenItem<V, E> {
	private final V mNode;
	private final ScopedHashMap<V, AstarAnnotation<E>> mAnnotations;
	private AstarAnnotation<E> mAnnotation;

	public OpenItem(V node, Map<V, AstarAnnotation<E>> annotations) {
		mNode = node;
		mAnnotations = new ScopedHashMap<>();
		for (final Entry<V, AstarAnnotation<E>> entry : annotations.entrySet()) {
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
