package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IntegerRestriction extends Restriction<Long> {
	private final int mValueCount;

	/**
	 * @param inequals     All specific values that the variable cannot take (have to be less than <strong>less</strong>
	 *                     and greater than <strong>greater</strong>),
	 * @param lessThan The value that the variable has to be smaller than (has to be strictly greater than
	 *                     <strong>less</strong>)
	 * @param greaterThan  The value that the variable has to be greater than
	 */
	public IntegerRestriction(final HashSet<Long> inequals, final Long lessThan, final Long greaterThan) {
		super(inequals, lessThan, greaterThan);
		assert lessThan > greaterThan + 1;

		final long possibleValueCount = (lessThan - greaterThan - 1) - inequals.size();
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

	public Long getLess() {
		return mLess;
	}

	public Long getGreater() {
		return mGreater;
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join("L, ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + (mInequal.size() > 0 ? "L" : "") + "), " + mLess + "L, " + mGreater + "L)";
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<Long> iter = mInequal.iterator();
			inEqual.append(", n != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return mGreater + " < n < " + mLess + inEqual.toString();
	}
}