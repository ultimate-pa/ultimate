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
