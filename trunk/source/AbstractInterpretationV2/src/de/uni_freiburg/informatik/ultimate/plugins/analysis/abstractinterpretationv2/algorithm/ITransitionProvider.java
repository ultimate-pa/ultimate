/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE AbstractInterpretationV2 plug-in.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE AbstractInterpretationV2 plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE AbstractInterpretationV2 plug-in. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE AbstractInterpretationV2 plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE AbstractInterpretationV2 plug-in grant you additional permission
 * to convey the resulting work.
 */

package de.uni_freiburg.informatik.ultimate.plugins.analysis.abstractinterpretationv2.algorithm;

import java.util.Collection;

/**
 * A {@link ITransitionProvider} describes the successor/predecessor relation of a control flow graph.
 *
 * @param <ACTION>
 *            The type of transitions of the control flow graph.
 * @param <LOCATION>
 *            The type of locations/vertices of the control flow graph.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * @author Marius Greitschus (greitsch@informatik.uni-freiburg.de)
 */
public interface ITransitionProvider<ACTION, LOCATION> {

	/**
	 * @param action
	 *            The current transition.
	 * @param scope
	 *            The current scope.
	 * @return all outgoing transitions of the target of the current transition that can be taken when in the current
	 *         scope.
	 */
	Collection<ACTION> getSuccessors(ACTION action, ACTION scope);

	/**
	 * @param action
	 *            a transition.
	 * @param scope
	 *            the current scope of the analysis.
	 * @return true if the target of this transition is an error location.
	 */
	boolean isSuccessorErrorLocation(ACTION action, ACTION scope);

	/**
	 * @param action
	 *            the current transition.
	 * @return true if the given transition enters a new scope, false otherwise. True also implies that the current
	 *         transition is a call transition.
	 */
	boolean isEnteringScope(ACTION action);

	/**
	 * @param action
	 *            the current transition.
	 * @param scope
	 *            the current scope (i.e., a call transition)
	 * @return true if the given transition leaves the given scope, false otherwise.
	 */
	boolean isLeavingScope(ACTION action, ACTION scope);

	/**
	 * @param action
	 *            the current transition.
	 * @param call
	 *            some call transition.
	 * @return true iff <code>action</code> is a summary for <code>call</code>
	 */
	boolean isSummaryForCall(ACTION action, ACTION call);

	/**
	 * @param action
	 *            the current transition.
	 * @return true iff the given transition is a summary for which an implementation and thus a call transition exists.
	 */
	boolean isSummaryWithImplementation(ACTION action);

	/**
	 * @param action
	 *            the current transition.
	 * @return the source of the current transition.
	 */
	LOCATION getSource(ACTION action);

	/**
	 * @param action
	 *            the current transition.
	 * @return the target of the current transition.
	 */
	LOCATION getTarget(ACTION action);

	/**
	 * @param loc
	 *            the current location.
	 * @return all outgoing transitions of this location.
	 */
	Collection<ACTION> getSuccessorActions(LOCATION loc);

	/**
	 * @param call
	 *            a call transition.
	 * @return if call is a call transition, return the summary transition that represents the call.
	 */
	ACTION getSummaryForCall(ACTION call);

	/**
	 * @param current
	 *            the current transition.
	 * @return the name of the procedure after or during the execution of the given transition. For summary transitions,
	 *         this returns the name of the procedure that is summarized.
	 */
	String getProcedureName(ACTION current);

	/**
	 * @param action
	 *            The current transition.
	 * @return a String representation of the current transition.
	 */
	String toLogString(ACTION action);
}
