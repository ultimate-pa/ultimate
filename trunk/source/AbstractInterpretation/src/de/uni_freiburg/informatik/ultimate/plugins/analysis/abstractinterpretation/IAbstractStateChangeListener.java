/*
 * Copyright (C) 2014-2015 Christopher Dillo
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE AbstractInterpretation plug-in.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE AbstractInterpretation plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretation plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretation plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE AbstractInterpretation plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
