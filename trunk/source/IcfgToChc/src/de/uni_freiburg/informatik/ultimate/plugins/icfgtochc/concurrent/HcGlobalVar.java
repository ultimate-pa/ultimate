package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramNonOldVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Represents a global variable of a program.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class HcGlobalVar implements IHcReplacementVar {
	// Hash codes are multiplied by this number to reduce likelihood of collisions with other IHcReplacementVar
	// implementations. Each implementation uses a different value.
	private static final int HASH_PRIME = 59;

	private final IProgramNonOldVar mVariable;

	public HcGlobalVar(final IProgramNonOldVar variable) {
		mVariable = Objects.requireNonNull(variable);
	}

	public IProgramNonOldVar getVariable() {
		return mVariable;
	}

	@Override
	public Sort getSort() {
		return mVariable.getSort();
	}

	@Override
	public String toString() {
		return mVariable.toString();
	}

	@Override
	public int hashCode() {
		return HASH_PRIME * mVariable.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj || (obj instanceof final HcGlobalVar other && mVariable.equals(other.mVariable));
	}
}
