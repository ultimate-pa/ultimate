package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public interface ITransitionProvider<T> {

	Collection<T> getSuccessors(T elem);
	
	boolean isPostErrorLocation(T elem);
	
}
