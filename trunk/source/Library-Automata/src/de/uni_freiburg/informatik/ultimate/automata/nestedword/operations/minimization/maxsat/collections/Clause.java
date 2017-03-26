/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.automata.nestedword.operations.minimization.maxsat.collections;

import java.util.Arrays;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 * Clause used by the MAX-SAT solver. Although there is only one positive atom in Horn clauses, this class allows one to
 * use several positive atoms.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @param <V>
 *            Kind of objects that are used as variables.
 */
class Clause<V> {
	/*
	 * counters for true/false/neither clauses
	 * 
	 * TODO remove after debugging
	 */
	public static int trues = 0, falses = 0, neithers = 0;

	// default clause conditions
	private static final TrueClauseCondition TRUE_CLAUSE_CONDITION = new TrueClauseCondition();
	private static final FalseClauseCondition FALSE_CLAUSE_CONDITION = new FalseClauseCondition();
	private static final UndeterminedClauseCondition UNDETERMINED_CLAUSE_CONDITION = new UndeterminedClauseCondition();

	protected final V[] mPositiveAtoms;
	protected final V[] mNegativeAtoms;
	protected IClauseCondition mClauseCondition;
	private boolean mIsHorn;
	private final int mHashCode;

	public Clause(final AbstractMaxSatSolver<V> solver, final V[] positiveAtoms, final V[] negativeAtoms) {
		mPositiveAtoms = positiveAtoms;
		mNegativeAtoms = negativeAtoms;
		mHashCode = computeHashCode();
		updateClauseCondition(solver);
	}

	private int computeHashCode() {
		final int prime = 31;
		return Arrays.hashCode(mPositiveAtoms) + prime * Arrays.hashCode(mNegativeAtoms);
	}

	void updateClauseCondition(final AbstractMaxSatSolver<V> solver) {
		mClauseCondition = computeClauseCondition(solver);
	}

	/**
	 * Computes the clause condition.
	 * <p>
	 * TODO: do update only for newly changed variable
	 * <p>
	 * TODO: update arrays to move finished variables to the end?
	 * 
	 * @param solver
	 *            solver
	 * @return clause condition
	 */
	public IClauseCondition computeClauseCondition(final AbstractMaxSatSolver<V> solver) {
		ClauseStatus clauseStatus = ClauseStatus.NEITHER;
		int unsetAtoms = 0;
		int unitIndex = -1;
		boolean unitIsPositive = false;
		for (int i = 0; i < mPositiveAtoms.length; ++i) {
			final V var = mPositiveAtoms[i];
			final VariableStatus status = solver.getCurrentVariableStatus(var);
			switch (status) {
				case FALSE:
					// do nothing
					break;
				case TRUE:
					clauseStatus = ClauseStatus.TRUE;
					break;
				case UNSET:
					unsetAtoms++;
					unitIndex = i;
					unitIsPositive = true;
					break;
				default:
					throw new IllegalArgumentException();
			}
		}

		// is the current clause a Horn clause?
		mIsHorn = (unsetAtoms <= 1);

		if (clauseStatus == ClauseStatus.NEITHER) {
			for (int i = 0; i < mNegativeAtoms.length; ++i) {
				final V var = mNegativeAtoms[i];
				final VariableStatus status = solver.getCurrentVariableStatus(var);
				switch (status) {
					case FALSE:
						clauseStatus = ClauseStatus.TRUE;
						break;
					case TRUE:
						// do nothing
						break;
					case UNSET:
						unsetAtoms++;
						unitIndex = i;
						unitIsPositive = false;
						break;
					default:
						throw new IllegalArgumentException();
				}
			}
		}

		assert (unsetAtoms >= 0) && (unsetAtoms <= mPositiveAtoms.length + mNegativeAtoms.length);

		if (clauseStatus == ClauseStatus.TRUE) {
			// trivial 'true' clause
			trues++;
			return TRUE_CLAUSE_CONDITION;
		}

		if (unsetAtoms == 0 || clauseStatus == ClauseStatus.FALSE) {
			assert (clauseStatus != ClauseStatus.TRUE);
			// trivial 'false' clause
			falses++;
			return FALSE_CLAUSE_CONDITION;
		}

		assert (clauseStatus == ClauseStatus.NEITHER);
		neithers++;
		if (unsetAtoms == 1) {
			// pseudo-unit clause
			return new PseudoUnitClauseCondition(unitIndex, unitIsPositive);
		} else {
			// clause with several undetermined literals
			return UNDETERMINED_CLAUSE_CONDITION;
		}
	}

	public Pair<V, Boolean> getPropagatee() {
		final int propagateeIndex = mClauseCondition.getUnitIndex();
		final boolean propagateeIsPositive = (propagateeIndex >= 0);
		final V var;
		if (propagateeIsPositive) {
			var = mPositiveAtoms[propagateeIndex];
		} else {
			var = mNegativeAtoms[-(propagateeIndex + 1)];
		}
		return new Pair<V, Boolean>(var, propagateeIsPositive);
	}

	public boolean isEquivalentToFalse() {
		return mClauseCondition.getClauseStatus() == ClauseStatus.FALSE;
	}

	public boolean isEquivalentToTrue() {
		return mClauseCondition.getClauseStatus() == ClauseStatus.TRUE;
	}

	public boolean isPseudoUnit() {
		return mClauseCondition.isPseudoUnit();
	}

	/**
	 * Positive atoms. DO NOT EDIT THE ARRAY!
	 */
	public V[] getPositiveAtoms() {
		return mPositiveAtoms;
	}

	/**
	 * Negative atoms. DO NOT EDIT THE ARRAY!
	 */
	public V[] getNegativeAtoms() {
		return mNegativeAtoms;
	}

	public ClauseStatus getClauseStatus() {
		return mClauseCondition.getClauseStatus();
	}

	/**
	 * Yet unset literal.
	 * 
	 * @param solver
	 *            solver
	 * @return an atom that was not yet set
	 */
	public Pair<V, Boolean> getUnsetAtom(final AbstractMaxSatSolver<V> solver) {
		if (!mClauseCondition.isPseudoUnit()) {
			throw new IllegalArgumentException("not only one unset Atom");
		} else {
			for (final V var : mPositiveAtoms) {
				final VariableStatus status = solver.getCurrentVariableStatus(var);
				switch (status) {
					case TRUE:
					case FALSE:
						// do nothing
						break;
					case UNSET:
						return new Pair<V, Boolean>(var, true);
					default:
						throw new IllegalArgumentException();
				}
			}
			for (final V var : mNegativeAtoms) {
				final VariableStatus status = solver.getCurrentVariableStatus(var);
				switch (status) {
					case TRUE:
					case FALSE:
						// do nothing
						break;
					case UNSET:
						return new Pair<V, Boolean>(var, false);
					default:
						throw new IllegalArgumentException();
				}
			}
			throw new AssertionError("did not find unset atom");
		}
	}

	@Override
	public String toString() {
		final StringBuilder sb = new StringBuilder();
		Iterator<V> it = Arrays.asList(mNegativeAtoms).iterator();
		while (it.hasNext()) {
			sb.append(it.next());
			if (it.hasNext()) {
				sb.append(" /\\ ");
			}
		}
		if (mNegativeAtoms.length > 0) {
			sb.append(" --> ");
		}
		if (mPositiveAtoms.length == 0) {
			sb.append("false");
		} else {
			it = Arrays.asList(mPositiveAtoms).iterator();
			while (it.hasNext()) {
				sb.append(it.next());
				if (it.hasNext()) {
					sb.append(" \\/ ");
				}
			}
		}
		return sb.toString();
	}

	/**
	 * Returns the Horn status of the last evaluation of the clause. It is intended that this does not necessarily
	 * correspond to the current assignment.
	 * 
	 * @return true iff the clause is a Horn clause under the current assignment
	 */
	public boolean isHorn() {
		return mIsHorn;
	}

	/**
	 * Checks whether the clause is a Horn clause under the current assignment.
	 * 
	 * @deprecated The method is currently not used as we report the Horn status of the last evaluation time.
	 * @param solver
	 *            solver
	 * @return true iff the clause is a Horn clause under the current assignment
	 */
	@Deprecated
	public boolean isHornCurrent(final AbstractMaxSatSolver<V> solver) {
		boolean foundFirst = false;
		for (final V var : mPositiveAtoms) {
			final VariableStatus status = solver.getCurrentVariableStatus(var);
			switch (status) {
				case UNSET:
					if (foundFirst) {
						return false;
					}
					foundFirst = true;
					break;
				case FALSE:
					break;
				case TRUE:
					throw new IllegalArgumentException(
							"Do not call this method for clauses which are equivalent to 'true'.");
				default:
					throw new IllegalArgumentException();
			}
		}
		return true;
	}

	@Override
	public int hashCode() {
		return mHashCode;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final Clause<?> other = (Clause<?>) obj;
		if (!Arrays.equals(mNegativeAtoms, other.mNegativeAtoms)) {
			return false;
		}
		return Arrays.equals(mPositiveAtoms, other.mPositiveAtoms);
	}
}
