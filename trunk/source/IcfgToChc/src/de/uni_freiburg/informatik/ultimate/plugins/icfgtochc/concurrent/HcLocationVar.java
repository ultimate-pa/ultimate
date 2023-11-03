package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgToChcConcurrent.IHcReplacementVar;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HcLocationVar implements IHcReplacementVar {
	private final String mProcedure;
	private final int mIndex;
	private final Sort mSort;

	public HcLocationVar(final String procedure, final int index, final Sort sort) {
		mProcedure = procedure;
		mIndex = index;
		mSort = sort;
	}

	public String getProcedure() {
		return mProcedure;
	}

	public int getIndex() {
		return mIndex;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public String toString() {
		return "loc_" + IcfgToChcConcurrentUtils.getReadableString(mProcedure) + "_" + (mIndex + 1);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIndex, mProcedure);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof HcLocationVar)) {
			return false;
		}
		final HcLocationVar other = (HcLocationVar) obj;
		return mIndex == other.mIndex && mProcedure.equals(other.mProcedure);
	}
}
