package de.uni_freiburg.informatik.ultimate.icfgtransformer.heapseparator;

import java.util.Collections;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.modelcheckerutils.cfg.variables.IProgramVarOrConst;
import de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt.arrays.MultiDimensionalSort;

public class ArrayGroup {
	private final Set<IProgramVarOrConst> mArraysInThisGroup;
	private final int mDimensionality;

	public ArrayGroup(final Set<IProgramVarOrConst> block) {
		mArraysInThisGroup = Collections.unmodifiableSet(block);
		final MultiDimensionalSort mdSort = new MultiDimensionalSort(block.iterator().next().getSort());
		mDimensionality = mdSort.getDimension();
	}

	Set<IProgramVarOrConst> getArrays() {
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
		Set<IProgramVarOrConst> getArrays() {
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
