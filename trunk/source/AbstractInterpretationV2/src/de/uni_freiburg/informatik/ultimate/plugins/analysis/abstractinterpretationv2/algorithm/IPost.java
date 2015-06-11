package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;

import de.uni_freiburg.informatik.ultimate.model.IElement;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public interface IPost<T extends IElement> {

	Collection<T> post(T elem);
	
}
