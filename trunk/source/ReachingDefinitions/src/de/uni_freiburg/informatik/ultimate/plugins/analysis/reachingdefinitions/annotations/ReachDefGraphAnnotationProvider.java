package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

public class ReachDefGraphAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	private static final String sDefaultKey = "Default";
	public static final String sAnnotationName = "ReachingDefinition";

	private final String mAnnotationSuffix;

	private final HashSet<String> mKeys;

	public ReachDefGraphAnnotationProvider(String annotationSuffix) {
		mAnnotationSuffix = annotationSuffix;
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

	@SuppressWarnings("unchecked")
	@Override
	public T getAnnotation(IElement element, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		String key = sAnnotationName + " " + uniqueId;
		if (mAnnotationSuffix == null) {
			return (T) element.getPayload().getAnnotations().get(key);
		} else {
			return (T) element.getPayload().getAnnotations().get(key + " " + mAnnotationSuffix);
		}
	}

	@Override
	public void annotate(IElement node, T annotation, String uniqueId) {
		assert uniqueId != null && !uniqueId.isEmpty();
		mKeys.add(uniqueId);
		String key = sAnnotationName + " " + uniqueId;
		if (mAnnotationSuffix == null) {
			node.getPayload().getAnnotations().put(key, annotation);
		} else {
			node.getPayload().getAnnotations().put(key + " " + mAnnotationSuffix, annotation);
		}
	}

	@Override
	public List<T> getAllAnnotations(IElement element) {
		List<T> rtr = new ArrayList<>();
		for(String key : mKeys){
			T annot = getAnnotation(element, key);
			if(annot != null){
				rtr.add(annot);
			}
		}
		return rtr;
	}

}
