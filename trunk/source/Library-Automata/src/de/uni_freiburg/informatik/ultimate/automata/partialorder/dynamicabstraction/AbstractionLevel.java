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
 *            actually a set of Programvariables
 */

class AbstractionLevel<H> {
	public H mValue;
	public boolean mLocked;
	public ILattice<H> mLattice;

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
	public void addToAbstractionLevel(final AbstractionLevel<H> level, final H vars) {
		level.mValue = level.mLattice.supremum(level.mValue, vars);
	}

	/**
	 * Compare two abstraction levels
	 *
	 * @param lv1
	 *            abstraction level we want to compare
	 * @param lv2
	 *            abstraction level we want lv1 to compare with
	 * @return STRICTLY_SMALLER if lv1 < lv2, EQUAL if lv1 = lv2, STRICTLY_GREATER if lv1 > lv2, INCOMPARABLE otherwise
	 */
	public ComparisonResult compare(final H lv1, final H lv2) {
		return mLattice.compare(lv1, lv2);
	}

	/**
	 * return the set of protected variables constituting the abstraction's abstraction level
	 *
	 * @return the value of the abstraction level
	 */
	public H getValue() {
		return this.mValue;
	}

	/**
	 * return whether the abstraction level has already been assigned all corresponding variables
	 *
	 * @return true if the abstraction level is locked
	 */
	public boolean isLocked() {
		return this.mLocked;
	}
}