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
}
