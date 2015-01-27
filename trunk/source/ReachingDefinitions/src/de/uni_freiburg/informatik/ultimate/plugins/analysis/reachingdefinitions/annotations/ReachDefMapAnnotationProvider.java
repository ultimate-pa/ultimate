package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

public class ReachDefMapAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	private static final String sDefaultKey = "Default";
	private final HashMap<HashKey, T> mMap;
	private final HashSet<String> mKeys;

	public ReachDefMapAnnotationProvider() {
		mMap = new HashMap<>();
		mKeys = new HashSet<>();
		mKeys.add(sDefaultKey);
	}

	public T getAnnotation(IElement element) {
		return getAnnotation(element, sDefaultKey);
	}

	@Override
	public void annotate(IElement node, T annotation) {
		annotate(node, annotation, sDefaultKey);
	}

	@Override
	public T getAnnotation(IElement element, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		return mMap.get(new HashKey(element, uniqueId));
	}

	@Override
	public void annotate(IElement node, T annotation, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		mKeys.add(uniqueId);
		mMap.put(new HashKey(node, uniqueId), annotation);
	}

	@Override
	public List<T> getAllAnnotations(IElement element) {
		List<T> rtr = new ArrayList<>();
		for (String key : mKeys) {
			T annot = getAnnotation(element, key);
			if (annot != null) {
				rtr.add(annot);
			}
		}
		return rtr;
	}

	private class HashKey {
		private IElement element;
		private String uniqueId;

		private HashKey(IElement elem, String key) {
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

		@SuppressWarnings("unchecked")
		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (getClass() != obj.getClass())
				return false;
			HashKey other = (HashKey) obj;

			if (element == null) {
				if (other.element != null)
					return false;
			} else if (!element.equals(other.element))
				return false;
			if (uniqueId == null) {
				if (other.uniqueId != null)
					return false;
			} else if (!uniqueId.equals(other.uniqueId))
				return false;
			return true;
		}

		@Override
		public String toString() {
			return "[" + uniqueId + "] " + element;
		}
	}

}
