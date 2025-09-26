package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.ILocalProgramVar;
import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 * Represents a (procedure-)local variable of a program.
 *
 * As we model thread templates of concurrent programs as procedures, this class also implements
 * {@link IHcThreadSpecificVar}.
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 */
public final class HcLocalVar implements IHcThreadSpecificVar {
	// Hash codes are multiplied by this number to reduce likelihood of collisions with other IHcReplacementVar
	// implementations. Each implementation uses a different value.
	private static final int HASH_PRIME = 97;

	private final ILocalProgramVar mVariable;
	private final ThreadInstance mInstance;

	public HcLocalVar(final ILocalProgramVar variable, final ThreadInstance instance) {
		assert variable.getProcedure().equals(instance.getTemplateName());
		mVariable = Objects.requireNonNull(variable);
		mInstance = Objects.requireNonNull(instance);
	}

	public IProgramVar getVariable() {
		return mVariable;
	}

	@Override
	public ThreadInstance getThreadInstance() {
		return mInstance;
	}

	@Override
	public IHcThreadSpecificVar forInstance(final int instanceId) {
		return new HcLocalVar(mVariable, new ThreadInstance(mInstance.getTemplateName(), instanceId));
	}

	@Override
	public Sort getSort() {
		return mVariable.getSort();
	}

	@Override
	public String toString() {
		return IcfgToChcConcurrentUtils.getReadableString(mVariable) + (mInstance.getInstanceNumber() + 1);
	}

	@Override
	public int hashCode() {
		return HASH_PRIME * Objects.hash(mInstance, mVariable);
	}

	@Override
	public boolean equals(final Object obj) {
		return this == obj || (obj instanceof final HcLocalVar other && mInstance.equals(other.mInstance)
				&& mVariable.equals(other.mVariable));
	}
}
