package de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent;

import java.util.Objects;

import de.uni_freiburg.informatik.ultimate.lib.modelcheckerutils.cfg.variables.IProgramVar;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.icfgtochc.concurrent.IcfgToChcConcurrent.IHcReplacementVar;

/**
 *
 * @author Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 *
 */
public class HcGlobalVar implements IHcReplacementVar {
	private final IProgramVar mVariable;

	public HcGlobalVar(final IProgramVar variable) {
		mVariable = variable;
	}

	public IProgramVar getVariable() {
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
		return mVariable.hashCode();
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof HcGlobalVar)) {
			return false;
		}
		final HcGlobalVar other = (HcGlobalVar) obj;
		return Objects.equals(mVariable, other.mVariable);
	}
}
