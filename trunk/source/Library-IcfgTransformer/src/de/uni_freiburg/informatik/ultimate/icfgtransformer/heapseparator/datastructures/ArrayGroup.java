/*
 * Copyright (C) 2017-2018 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2017-2018 University of Freiburg
 *
 * This file is part of the ULTIMATE IcfgTransformer library.
 *
 * The ULTIMATE IcfgTransformer is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE IcfgTransformer is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE IcfgTransformer library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE IcfgTransformer library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE IcfgTransformer grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator.datastructures;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.smt.arrays.MultiDimensionalSort;
import de.uni_freiburg.informatik.ultimate.logic.TermVariable;

/**
 * The purpose of array groups is to enable the restriction of the separation to some arrays (the "heap arrays").
 * I.e., array groups will be used to determine for a given {@link TermVariable} or {@link IProgramVarOrConst}, if it
 *  is subject to heap/array separation (e.g. a loc-array should be introduced for it).
 *  <p>
 * Historical comments:
 * ArrayGroups are not
 * <ul>
 *  <li> about "aligning" sub-arrays
 *  <li> about tracking which arrays are assumed equal in the program (we do not handle programs with assumes between
 *    heap arrays)
 * </ul>
 *
 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
 *
 */
public class ArrayGroup {
	private final Set<IProgramVarOrConst> mArraysInThisGroup;
	private final int mDimensionality;

	public ArrayGroup(final Set<IProgramVarOrConst> block) {
		mArraysInThisGroup = Collections.unmodifiableSet(block);
		final MultiDimensionalSort mdSort = new MultiDimensionalSort(block.iterator().next().getSort());
		mDimensionality = mdSort.getDimension();
	}

	public Set<IProgramVarOrConst> getArrays() {
		return mArraysInThisGroup;
	}

	@Override
	public String toString() {
		return mArraysInThisGroup.toString();
	}

	public int getDimensionality() {
		return mDimensionality;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mArraysInThisGroup == null) ? 0 : mArraysInThisGroup.hashCode());
		return result;
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
		final ArrayGroup other = (ArrayGroup) obj;
		if (mArraysInThisGroup == null) {
			if (other.mArraysInThisGroup != null) {
				return false;
			}
		} else if (!mArraysInThisGroup.equals(other.mArraysInThisGroup)) {
			return false;
		}
		return true;
	}

	/*
	 * return the dummy ArrayGroup
	 */
	public static ArrayGroup getNoArrayGroup() {
		return new NoArrayGroup();
	}

	/**
	 * Dummy class. The Array group that aux vars in Transformulas belong to which are never equated to some pvoc.
	 *
	 * @author Alexander Nutz (nutz@informatik.uni-freiburg.de)
	 *
	 */
	private static class NoArrayGroup extends ArrayGroup {

		public NoArrayGroup() {
			super(Collections.emptySet());
		}

		@Override
		public Set<IProgramVarOrConst> getArrays() {
			return Collections.emptySet();
		}

		@Override
		public String toString() {
			return "NoArrayGroup";
		}

		@Override
		public int getDimensionality() {
			return -1;
		}

		@Override
		public int hashCode() {
			return 0;
		}

		@Override
		public boolean equals(final Object obj) {
			if (!(obj instanceof NoArrayGroup)) {
				return false;
			}
			return true;
		}
	}
}
