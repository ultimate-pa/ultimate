package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IntegerRestriction extends Restriction<Integer> {
	private final int mValueCount;

	/**
	 * @param inequal All specific values that the variable cannot take (have to be less than <strong>less</strong> and
	 *                greater than <strong>greater</strong>),
	 * @param less    The value that the variable has to be smaller than (has to be strictly greater than
	 *                <strong>less</strong>)
	 * @param greater The value that the variable has to be greater than
	 */
	public IntegerRestriction(final HashSet<Integer> inequal, final int less, final int greater) {
		super(inequal, less, greater);
		assert less > greater + 1;

		final long possibleValueCount = (less - (long) greater - 1) - inequal.size();
		if (possibleValueCount > Integer.MAX_VALUE) {
			mValueCount = Integer.MAX_VALUE;
		} else {
			mValueCount = (int) possibleValueCount;
		}
		assert mValueCount > 0;
	}

	public Integer getValueCount() {
		return mValueCount;
	}

	public int getLess() {
		return mLess;
	}

	public int getGreater() {
		return mGreater;
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join(", ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + "), " + mLess + ", " + mGreater + ")";
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<Integer> iter = mInequal.iterator();
			inEqual.append(", n != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return mGreater + " < n < " + mLess + inEqual.toString();
	}
}