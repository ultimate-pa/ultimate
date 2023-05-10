package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HcLocalVar implements IHcThreadSpecificVar {
	private final IProgramVar mVariable;
	private final ThreadInstance mInstance;

	public HcLocalVar(final IProgramVar variable, final ThreadInstance instance) {
		assert variable.getProcedure().equals(instance.getTemplateName());
		mVariable = variable;
		mInstance = instance;
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
		final int prime = 97;
		return prime * Objects.hash(mInstance, mVariable);
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
		final HcLocalVar other = (HcLocalVar) obj;
		return Objects.equals(mInstance, other.mInstance) && Objects.equals(mVariable, other.mVariable);
	}
}
