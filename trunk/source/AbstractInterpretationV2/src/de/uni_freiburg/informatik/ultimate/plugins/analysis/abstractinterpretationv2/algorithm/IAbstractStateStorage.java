/*
 * Copyright (C) 2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
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

import java.util.Deque;
import java.util.Map;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.DisjunctiveAbstractState;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.absint.IAbstractState;
import de.uni_freiburg.informatik.ultimate.logic.Term;

/**
 * An {@link IAbstractStateStorage} allows to store the relation between abstract states, program locations (of a
 * control flow graph), and scopes.
 *
 * It also provides methods to convert all abstract states stored at a location to {@link Term}s.
 *
 * A {@link IAbstractStateStorage} instance is relative to one scope stack and retains links to its parent abstract
 * state storage.
 *
 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 *
 */
public interface IAbstractStateStorage<STATE extends IAbstractState<STATE>, ACTION, LOC> {

	/**
	 * @param loc
	 *            a location.
	 * @return an {@link DisjunctiveAbstractState} that represents multiple abstract states that were saved at the given
	 *         location.
	 */
	DisjunctiveAbstractState<STATE> getAbstractState(LOC loc);

	/**
	 * Save a new state to some location. If there is already a state, merge the new one with the old one according to
	 * the concrete implementation (e.g., respecting parallel states).
	 *
	 * @param loc
	 *            the location to which the state should be saved
	 * @param state
	 *            the state that should be saved.
	 * @return The new state that is now saved at this location (i.e., either the given state or a merged state).
	 */
	DisjunctiveAbstractState<STATE> addAbstractState(LOC loc, DisjunctiveAbstractState<STATE> state);

	IAbstractStateStorage<STATE, ACTION, LOC> createStorage(ACTION scope);

	void scopeFixpointReached();

	void saveSummarySubstituion(ACTION action, DisjunctiveAbstractState<STATE> summaryPostState, ACTION summaryAction);

	/**
	 * Computes a mapping that assigns each location a term. The term represents the fixpoint computed at this location
	 * according to the selected domain and analysis type. Locations that do not occur in the map were not reached.
	 *
	 * @return a map from location to term.
	 */
	Map<LOC, Set<DisjunctiveAbstractState<STATE>>> computeLoc2States();

	/**
	 * Get the set of abstract domain states that is saved at the target location of the given symbol in the context
	 * given by a call stack.
	 *
	 * @param callStack
	 *            A stack of calls representing a context.
	 * @param symbol
	 *            The current transition.
	 * @return The set of states saved at this location in this context or the empty set if no state is saved at this
	 *         location.
	 */
	Set<STATE> computeContextSensitiveAbstractPostStates(Deque<ACTION> callStack, ACTION symbol);
}
