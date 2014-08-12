package de.uni_freiburg.informatik.ultimate.plugins.analysis.reachingdefinitions.annotations;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * @author dietsch
 *
 * @param <T>
 */
public interface IAnnotationProvider<T> {
	
	public T getAnnotation(IElement element);
	
	public void annotate(IElement node, T annotation);

}
