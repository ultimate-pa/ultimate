package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;

/**
 * 
 * @author dietsch@informatik.uni-freiburg.de
 * @author greitsch@informatik.uni-freiburg.de
 *
 */
public interface ITransitionProvider<ACTION> {

	Collection<ACTION> filterInitialElements(Collection<ACTION> actions);

	Collection<ACTION> getSuccessors(ACTION current, ACTION scope);

	boolean isPostErrorLocation(ACTION current, ACTION scope);

	String toLogString(ACTION elem);

	boolean isEnteringScope(ACTION current);

	boolean isLeavingScope(ACTION current, ACTION scope);
}
