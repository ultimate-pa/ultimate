/*
 * Copyright (C) 2017 Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Copyright (C) 2017 University of Freiburg
 * 
 * This file is part of the ULTIMATE Automata Library.
 * 
 * The ULTIMATE Automata Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE Automata Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Automata Library. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Automata Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Automata Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * This interface is intended for interactive modules in a partial Max-SAT solver. Whenever the solver makes an
 * assignment, it informs all its interactive modules and receives back a list of new assignments that follow from all
 * current assignments.
 * 
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 * @param <T>
 *            type of the content wrapper in pairs (controlled by implementing subclass)
 */
public interface IAssignmentCheckerAndGenerator<T> {
	/**
	 * @param var
	 *            New Variable.
	 */
	void addVariable(final T var);

	/**
	 * The solver guarantees that it will never backtrack beyond the current assignments, i.e., all scopes can be
	 * removed and assignments can be made permanent, if supported.
	 * <p>
	 * This method only exists for performance reasons. An implementing class may safely ignore this method.
	 */
	void makeAssignmentsPersistent();

	/**
	 * Adds a new backtracking point.
	 * 
	 * @see #revertOneScope()
	 */
	void addScope();

	/**
	 * Undoes all assignments since the previous opening of a scope.
	 * 
	 * @see #addScope()
	 */
	void revertOneScope();

	/**
	 * If an implementing class wants to report a contradiction, it just has to return the same variable with the
	 * opposite status.
	 * 
	 * @param var
	 *            variable
	 * @param newStatus
	 *            new status of the variable
	 * @return a list of variable-status-pairs s.t. the new status follows from the theory context
	 */
	Iterable<Pair<T, Boolean>> checkAssignment(T var, boolean newStatus);
}
