package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.Iterator;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;

public class IntegerRestriction extends Restriction<Long> {
	private final Long mValidValueCount;
	private final long mRangeSize;

	public IntegerRestriction(final HashSet<Long> inequals, final Long minimum, final Long maximum) {
		super(inequals, minimum, maximum);
		assert mMinimum <= mMaximum;

		mRangeSize = Util.addSafe(Util.subtractSafe(mMaximum, mMinimum), 1); // number of values := max - min + 1
		mValidValueCount = mRangeSize - mInequal.size();
		assert mValidValueCount > 0;
	}

	public Long getValueCount() {
		return mValidValueCount;
	}

	public Long getMinimum() {
		return mMinimum;
	}

	public Long getMaximum() {
		return mMaximum;
	}

	public Long getNthValue(final long n) {
		assert 0 <= n && n < mValidValueCount;
		long currentValue = mMinimum + n;
		long skipped = 0;
		boolean contained = mInequal.contains(currentValue);

		while (contained || skipped > 0) {
			if (!contained) {
				skipped--;
			} else {
				skipped++;
			}
			currentValue++;
			if (currentValue >= mMaximum) {
				currentValue -= mRangeSize;
			}
			contained = mInequal.contains(currentValue);
		}
		assert mMinimum <= currentValue && currentValue <= mMaximum;
		return currentValue;
	}

	public static Long findMinimum(final Long... minimums) {
		if (minimums.length == 0) {
			return Long.MIN_VALUE;
		}
		Long smallest = minimums[0];
		for (final Long lessThen : minimums) {
			smallest = smallest > lessThen ? lessThen : smallest;
		}
		return smallest;
	}

	public static Long findMaximum(final Long... maximums) {
		if (maximums.length == 0) {
			return Long.MAX_VALUE;
		}
		Long greatest = maximums[0];
		for (final Long greaterThen : maximums) {
			greatest = greatest < greaterThen ? greaterThen : greatest;
		}
		return greatest;
	}

	public static IntegerRestriction makeRestriction(final Long minimum, final Long maximum, final Long... inEquals) {
		final HashSet<Long> inEqualSet = new HashSet<>();

		for (final Long inEqual : inEquals) {
			if (minimum <= inEqual && inEqual <= maximum) {
				inEqualSet.add(inEqual);
			}
		}

		return new IntegerRestriction(inEqualSet, minimum, maximum);
	}

	@Override
	public String toCode() {
		return "new " + this.getClass().getSimpleName() + "(Util.toHashSet("
				+ String.join("L, ", Util.map(mInequal, (inequal) -> {
					return inequal.toString();
				}, new ArrayList<>())) + (mInequal.size() > 0 ? "L" : "") + "), " + mMinimum + "L, " + mMaximum + "L)";
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

		return mMaximum + " < n < " + mMinimum + inEqual.toString();
	}
}