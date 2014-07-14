/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.model.IElement;
import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;

/**
 * Abstract state change listeners can register with the AbstractInterpreter and will
 * be notified if an abstract state at a node changes, getting access to the old
 * state, the incoming new state and the merged/widened state if applicable.
 * 
 * @author Christopher Dillo
 */
public interface IAbstractStateChangeListener {
	public void onStateChange(IElement location, List<AbstractState> oldStates, AbstractState newState, AbstractState mergedState);
}
