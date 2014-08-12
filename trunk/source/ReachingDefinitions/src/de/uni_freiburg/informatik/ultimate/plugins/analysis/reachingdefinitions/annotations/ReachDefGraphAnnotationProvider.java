package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import de.uni_freiburg.informatik.ultimate.model.IElement;

public class ReachDefGraphAnnotationProvider<T extends ReachDefBaseAnnotation> implements IAnnotationProvider<T> {

	public static final String sAnnotationName = "ReachingDefinition";
	
	private final String mAnnotationSuffix;
	
	public ReachDefGraphAnnotationProvider(String annotationSuffix){
		mAnnotationSuffix = annotationSuffix;
	}

	@SuppressWarnings("unchecked")
	public T getAnnotation(IElement element) {
		if (!element.hasPayload()) {
			return null;
		}
		if (!element.getPayload().hasAnnotation()) {
			return null;
		}
		if (mAnnotationSuffix == null) {
			return (T) element.getPayload().getAnnotations().get(sAnnotationName);
		} else {
			return (T) element.getPayload().getAnnotations().get(sAnnotationName + " " + mAnnotationSuffix);
		}

	}

	@Override
	public void annotate(IElement node, T annotation) {
		if (mAnnotationSuffix == null) {
			node.getPayload().getAnnotations().put(sAnnotationName, annotation);
		} else {
			node.getPayload().getAnnotations().put(sAnnotationName + " " + mAnnotationSuffix, annotation);
		}
	}


}
