/**
 * 
 */
package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation;

import java.util.List;

import de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretation.abstractdomain.AbstractState;
import de.uni_freiburg.informatik.ultimate.plugins.generator.rcfgbuilder.cfg.RCFGEdge;

/**
 * Abstract state change listeners can register with the AbstractInterpreter and will
 * be notified if an abstract state at a node changes, getting access to the old
 * state, the incoming new state and the merged/widened state if applicable.
 * 
 * @author Christopher Dillo
 */
public interface IAbstractStateChangeListener {
	/**
	 * @param viaEdge The edge that changed the state
	 * @param oldStates A list of old states. May be null if no old states exist.
	 * @param newState The new state which arrived at the location.
	 * @param mergedState The merged state. Same as the new state if no merging happened.
	 */
	public void onStateChange(RCFGEdge viaEdge, List<AbstractState> oldStates, AbstractState newState, AbstractState mergedState);
}
