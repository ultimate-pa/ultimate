package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HcLocationVar implements IHcThreadSpecificVar {
	private final ThreadInstance mInstance;
	private final Sort mSort;

	public HcLocationVar(final ThreadInstance instance, final Sort sort) {
		mInstance = instance;
		mSort = sort;
	}

	@Override
	public ThreadInstance getThreadInstance() {
		return mInstance;
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public String toString() {
		return "loc_" + IcfgToChcConcurrentUtils.getReadableString(mInstance.getTemplateName()) + "_"
				+ (mInstance.getInstanceNumber() + 1);
	}

	@Override
	public int hashCode() {
		final int prime = 79;
		return prime * Objects.hash(mInstance);
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
		final HcLocationVar other = (HcLocationVar) obj;
		return Objects.equals(mInstance, other.mInstance);
	}
}
