package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Models the program counter of a program. I.e., this variable is used to store an integer encoding the current control
 * location of a sequential program resp. the current control location of a thread in a concurrent program.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class HcLocationVar implements IHcThreadSpecificVar {
	// Hash codes are multiplied by this number to reduce likelihood of collisions with other IHcReplacementVar
	// implementations. Each implementation uses a different value.
	private static final int HASH_PRIME = 79;

	private final ThreadInstance mInstance;
	private final Sort mSort;

	public HcLocationVar(final ThreadInstance instance, final Script script) {
		this(instance, SmtSortUtils.getIntSort(script));
	}

	private HcLocationVar(final ThreadInstance instance, final Sort sort) {
		mInstance = Objects.requireNonNull(instance);
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
		return HASH_PRIME * Objects.hash(mInstance);
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj || (obj instanceof final HcLocationVar other && mInstance.equals(other.mInstance));
	}
}
