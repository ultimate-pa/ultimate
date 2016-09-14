/*
 * Copyright (C) 2014-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE ReachingDefinitions plug-in.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE ReachingDefinitions plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ReachingDefinitions plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ReachingDefinitions plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ReachingDefinitions plug-in grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.models.IElement;

public class ReachDefMapAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	private static final String sDefaultKey = "Default";
	private final HashMap<HashKey, T> mMap;
	private final HashSet<String> mKeys;

	public ReachDefMapAnnotationProvider() {
		mMap = new HashMap<>();
		mKeys = new HashSet<>();
		mKeys.add(sDefaultKey);
	}

	@Override
	public T getAnnotation(final IElement element) {
		return getAnnotation(element, sDefaultKey);
	}

	@Override
	public void annotate(final IElement node, final T annotation) {
		annotate(node, annotation, sDefaultKey);
	}

	@Override
	public T getAnnotation(final IElement element, final String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		return mMap.get(new HashKey(element, uniqueId));
	}

	@Override
	public void annotate(final IElement node, final T annotation, final String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		mKeys.add(uniqueId);
		mMap.put(new HashKey(node, uniqueId), annotation);
	}

	@Override
	public List<T> getAllAnnotations(final IElement element) {
		final List<T> rtr = new ArrayList<>();
		for (final String key : mKeys) {
			final T annot = getAnnotation(element, key);
			if (annot != null) {
				rtr.add(annot);
			}
		}
		return rtr;
	}

	private static final class HashKey {
		private final IElement element;
		private final String uniqueId;

		HashKey(final IElement elem, final String key) {
			element = elem;
			uniqueId = key;
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result + ((element == null) ? 0 : element.hashCode());
			result = prime * result + ((uniqueId == null) ? 0 : uniqueId.hashCode());
			return result;
		}

		@Override
		public boolean equals(final Object obj) {
			if (this == obj) {
				return true;
			}
			if (obj == null) {
				return false;
			}
			if (getClass() != obj.getClass()) {
				return false;
			}
			final HashKey other = (HashKey) obj;

			if (element == null) {
				if (other.element != null) {
					return false;
				}
			} else if (!element.equals(other.element)) {
				return false;
			}
			if (uniqueId == null) {
				if (other.uniqueId != null) {
					return false;
				}
			} else if (!uniqueId.equals(other.uniqueId)) {
				return false;
			}
			return true;
		}

		@Override
		public String toString() {
			return "[" + uniqueId + "] " + element;
		}
	}

}
