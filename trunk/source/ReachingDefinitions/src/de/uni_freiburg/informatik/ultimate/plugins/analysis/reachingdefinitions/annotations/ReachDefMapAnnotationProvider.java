package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.model.IElement;

public class ReachDefMapAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	private final HashMap<IElement, T> mMap;

	public ReachDefMapAnnotationProvider() {
		mMap = new HashMap<>();
	}

	public T getAnnotation(IElement element) {
		return mMap.get(element);
	}

	@Override
	public void annotate(IElement node, T annotation) {
		mMap.put(node, annotation);
	}

}
