package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HcLocationVar implements IHcThreadSpecificVar {
	private final ThreadInstance mInstance;
	private final Sort mSort;

	public HcLocationVar(final ThreadInstance instance, final Script script) {
		this(instance, SmtSortUtils.getIntSort(script));
	}

	private HcLocationVar(final ThreadInstance instance, final Sort sort) {
		mInstance = instance;
		mSort = sort;
	}

	@Override
	public ThreadInstance getThreadInstance() {
		return mInstance;
	}

	@Override
	public IHcThreadSpecificVar forInstance(final int instanceId) {
		return new HcLocationVar(new ThreadInstance(mInstance.getTemplateName(), instanceId), mSort);
	}

	@Override
	public Sort getSort() {
		return mSort;
	}

	@Override
	public String toString() {
		return "loc_" + mInstance;
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
