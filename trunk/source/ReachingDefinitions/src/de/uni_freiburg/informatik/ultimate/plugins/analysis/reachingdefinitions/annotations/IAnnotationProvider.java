package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * @author dietsch
 * 
 * @param <T>
 */
public interface IAnnotationProvider<T> {

	public T getAnnotation(IElement element);

	public T getAnnotation(IElement element, String uniqueId);

	/**
	 * Return all annotations that were made with this provider for this element
	 * regardless of key
	 */
	public List<T> getAllAnnotations(IElement element);

	public void annotate(IElement node, T annotation);

	public void annotate(IElement node, T annotation, String uniqueId);

}
