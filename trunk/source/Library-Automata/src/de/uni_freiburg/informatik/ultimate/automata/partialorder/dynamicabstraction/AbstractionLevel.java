/*
 * Copyright (C) 2023 Veronika Klasen
 * Copyright (C) 2023 University of Freiburg
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

package de.uni_freiburg.informatik.ultimate.automata.partialorder.dynamicabstraction;

import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.ILattice;
import de.uni_freiburg.informatik.ultimate.util.datastructures.poset.IPartialComparator.ComparisonResult;

/**
 * The abstraction levels for DynamicStratifiedReduction
 *
 * @param <H>
 *            actually a set of program variables
 */

public class AbstractionLevel<H> {
	private H mValue;
	private boolean mLocked;
	private final ILattice<H> mLattice;

	/**
	 * @param protectedVar
	 *            variables the abstraction is forbidden from abstracting
	 * @param lattice
	 *
	 * @param true
	 *            if the value of the abstraction level is fixed from now on
	 */
	public AbstractionLevel(final H protectedVar, final ILattice<H> lattice, final boolean locked) {
		mValue = protectedVar;
		mLocked = locked;
		mLattice = lattice;
	}

	/**
	 * Add additional variables to an abstraction level's value
	 *
	 * @param level
	 *            the abstraction level
	 * @param vars
	 *            the variables to be added
	 */
	public void addToAbstractionLevel(final H vars) {
		mValue = mLattice.infimum(mValue, vars);
	}

	/**
	 * Lock an abstraction level
	 */

	public void lock() {
		mLocked = true;
	}

	/**
	 * Compare two abstraction levels
	 *
	 * @param level
	 *            abstraction level we want to compare with
	 * @return STRICTLY_SMALLER if < level, EQUAL if = level, STRICTLY_GREATER if > level, INCOMPARABLE otherwise
	 */
	public ComparisonResult compare(final H level) {
		return mLattice.compare(mValue, level);
	}

	/**
	 * return the set of protected variables constituting the abstraction's abstraction level
	 *
	 * @return the value of the abstraction level
	 */
	public H getValue() {
		return mValue;
	}

	public ILattice<H> getLattice() {
		return mLattice;

	}

	/**
	 * return whether the abstraction level has already been assigned all corresponding variables
	 *
	 * @return true if the abstraction level is locked
	 */
	public boolean isLocked() {
		return mLocked;
	}
}