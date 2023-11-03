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
public class HcLocalVar implements IHcReplacementVar {
	private final IProgramVar mVariable;
	private final int mIndex;

	public HcLocalVar(final IProgramVar variable, final int index) {
		mVariable = variable;
		mIndex = index;
	}

	public IProgramVar getVariable() {
		return mVariable;
	}

	public int getIndex() {
		return mIndex;
	}

	public String getProcedure() {
		return mVariable.getProcedure();
	}

	@Override
	public Sort getSort() {
		return mVariable.getSort();
	}

	@Override
	public String toString() {
		return IcfgToChcConcurrentUtils.getReadableString(mVariable) + (mIndex + 1);
	}

	@Override
	public int hashCode() {
		return Objects.hash(mIndex, mVariable);
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (!(obj instanceof HcLocalVar)) {
			return false;
		}
		final HcLocalVar other = (HcLocalVar) obj;
		return mIndex == other.mIndex && mVariable.equals(other.mVariable);
	}
}
