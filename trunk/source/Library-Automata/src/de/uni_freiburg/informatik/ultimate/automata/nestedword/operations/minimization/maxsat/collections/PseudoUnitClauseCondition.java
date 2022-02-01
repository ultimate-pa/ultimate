/*
 * Copyright (C) 2016 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2016 Christian Schilling (schillic@informatik.uni-freiburg.de)
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

/**
 * Clause condition for clause with exactly one literal with undetermined truth value. This literal is also called
 * pseudo-unit.
 * 
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * @author Christian Schilling (schillic@informatik.uni-freiburg.de)
 */
public final class PseudoUnitClauseCondition implements IClauseCondition {
	private final int mUnitIndex;

	/**
	 * Constructor.
	 * 
	 * @param unitIndex
	 *            index of the unit literal (only if 'unsetAtoms == 1')
	 * @param unitIsPositive
	 *            true iff the unit literal is positive (only if 'unsetAtoms == 1')
	 */
	public PseudoUnitClauseCondition(final int unitIndex, final boolean unitIsPositive) {
		if (unitIsPositive) {
			mUnitIndex = unitIndex;
		} else {
			mUnitIndex = -unitIndex - 1;
		}
	}

	@Override
	public boolean isPseudoUnit() {
		return true;
	}

	@Override
	public int getUnitIndex() {
		return mUnitIndex;
	}

	@Override
	public int hashCode() {
		// should never be hashed
		throw new AssertionError();
	}

	@Override
	public boolean equals(final Object other) {
		// should never be compared
		throw new AssertionError();
	}

	@Override
	public String toString() {
		return "ClauseCondition [mClauseStatus=" + getClauseStatus() + ", mUnsetAtoms=1, propagateeIndex=" + mUnitIndex
				+ "]";
	}
}
