/*
 * Copyright (C) 2016 Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * Copyright (C) 2016 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.automata.nwalibrary.operations.minimization.maxsat2;

import java.util.Arrays;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Clause used by the MAX-SAT solver. Although there is only one
 * positive atom in Horn clauses, this class allows one to use
 * several positive atoms.
 * 
 * @author Matthias Heizmann <heizmann@informatik.uni-freiburg.de>
 * @param <V> Kind of objects that are used as variables.
 */
class Clause<V> {
	protected final V[] mPositiveAtoms;
	protected final V[] mNegativeAtoms;
	protected ClauseCondition mClauseCondition;
	
	public Clause(final AMaxSatSolver<V> solver, final V[] positiveAtoms, final V[] negativeAtoms) {
		mPositiveAtoms = positiveAtoms;
		mNegativeAtoms = negativeAtoms;
		updateClauseCondition(solver);
	}
	
	void updateClauseCondition(final AMaxSatSolver<V> solver) {
		mClauseCondition = computeClauseCondition(solver);
	}

	/**
	 * TODO: do update only for newly changed variable
	 * 
	 * @param solver solver
	 * @return clause condition
	 */
	public ClauseCondition computeClauseCondition(final AMaxSatSolver<V> solver) {
		EClauseStatus clauseStatus = EClauseStatus.NEITHER;
		int unsetAtoms = 0;
		for (final V var : mPositiveAtoms) {
			final EVariableStatus status = getCurrentVariableStatus(var, solver);
			switch (status) {
			case FALSE:
				// do nothing
				break;
			case TRUE:
				clauseStatus = EClauseStatus.TRUE;
				break;
			case UNSET:
				unsetAtoms++;
				break;
			default:
				throw new AssertionError();
			}
		}
		for (final V var : mNegativeAtoms) {
			final EVariableStatus status = getCurrentVariableStatus(var, solver);
			switch (status) {
			case FALSE:
				clauseStatus = EClauseStatus.TRUE;
				break;
			case TRUE:
				// do nothing
				break;
			case UNSET:
				unsetAtoms++;
				break;
			default:
				throw new AssertionError();
			}
		}
		assert unsetAtoms >= 0 && unsetAtoms <= mPositiveAtoms.length + mNegativeAtoms.length;
		if (unsetAtoms == 0 && clauseStatus != EClauseStatus.TRUE) {
			clauseStatus = EClauseStatus.FALSE;
		}
		return new ClauseCondition(clauseStatus, unsetAtoms);
	}
	
	private EVariableStatus getCurrentVariableStatus(final V var, final AMaxSatSolver<V> solver) {
		assert solver.mVariables.contains(var);
		final Boolean irr = solver.getPersistentAssignment(var);
		if (irr != null) {
			if (irr) {
				return EVariableStatus.TRUE;
			} else {
				return EVariableStatus.FALSE;
			}
		}
		final Boolean tmp = solver.getTemporaryAssignment(var);
		if (tmp != null) {
			if (tmp) {
				return EVariableStatus.TRUE;
			} else {
				return EVariableStatus.FALSE;
			}
		}
		return EVariableStatus.UNSET;
	}

	public boolean isEquivalentToFalse() {
		return mClauseCondition.getClauseStatus() == EClauseStatus.FALSE;
	}
	
	public boolean isEquivalentToTrue() {
		return mClauseCondition.getClauseStatus() == EClauseStatus.TRUE;
	}
	
	public int getUnsetAtoms() {
		return mClauseCondition.getUnsetAtoms();
	}

	public V[] getPositiveAtoms() {
		return mPositiveAtoms;
	}

	public V[] getNegativeAtoms() {
		return mNegativeAtoms;
	}
	
	public ClauseCondition getClauseCondition() {
		return mClauseCondition;
	}

	/**
	 * @param solver solver
	 * @return an atom that was not yet set
	 */
	public Pair<V,Boolean> getUnsetAtom(final AMaxSatSolver<V> solver) {
		if (mClauseCondition.getUnsetAtoms() != 1) {
			throw new IllegalArgumentException("not only one unset Atom");
		} else {
			for (final V var : mPositiveAtoms) {
				final EVariableStatus status = getCurrentVariableStatus(var, solver);
				switch (status) {
				case TRUE:
				case FALSE:
					// do nothing
					break;
				case UNSET:
					return new Pair<V, Boolean>(var, true);
				default:
					throw new AssertionError();
				}
			}
			for (final V var : mNegativeAtoms) {
				final EVariableStatus status = getCurrentVariableStatus(var, solver);
				switch (status) {
				case TRUE:
				case FALSE:
					// do nothing
					break;
				case UNSET:
					return new Pair<V, Boolean>(var, false);
				default:
					throw new AssertionError();
				}
			}
			throw new AssertionError("did not find unset atom");
		}
	}
	
	public boolean isPropagatee() {
		return mClauseCondition.getUnsetAtoms() == 1 && 
				mClauseCondition.getClauseStatus() != EClauseStatus.TRUE;
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		Iterator<V> it = Arrays.asList(mNegativeAtoms).iterator();
		while(it.hasNext()) {
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(" /\\ ");
			}
		}
		if (mNegativeAtoms.length > 0 && mPositiveAtoms.length > 0) {
			sb.append(" --> ");
		}
		it = Arrays.asList(mPositiveAtoms).iterator();
		while(it.hasNext()) {
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(" \\/ ");
			}
		}
		return sb.toString();
	}

	/**
	 * @return true iff the clause is a Horn clause under the current assignment
	 */
	public boolean isHorn(final AMaxSatSolver<V> solver) {
		boolean foundFirst = false;
		for (final V var : mPositiveAtoms) {
			final EVariableStatus status = getCurrentVariableStatus(var, solver);
			switch (status) {
				case TRUE:
					if (foundFirst) {
						return false;
					}
					foundFirst = true;
					break;
				case FALSE:
				case UNSET:
					break;
				default:
					throw new AssertionError();
			}
		}
		return true;
	}
	
}
