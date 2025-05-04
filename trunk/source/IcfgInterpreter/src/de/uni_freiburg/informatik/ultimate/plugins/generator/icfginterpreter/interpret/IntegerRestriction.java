package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;

public class IntegerRestriction extends Restriction<IntValue> {
	private final IntValue mValidValueCount;
	private final IntValue mRangeSize;

	public IntegerRestriction(final Set<IntValue> inequals, final IntValue minimum, final IntValue maximum) {
		super(inequals, minimum, maximum);
		if (mMinimum == null || mMaximum == null) {
			mRangeSize = null;
			mValidValueCount = null;
		} else {
			assert mMinimum.compareTo(mMaximum) <= 0;
			mRangeSize = mMaximum.subtract(mMinimum).add(IntValue.ONE); // number of values := max - min + 1
			mValidValueCount = mRangeSize.subtract(new IntValue(BigInteger.valueOf(mInequal.size())));
			assert IntValue.ZERO.compareTo(mValidValueCount) < 0;
		}
	}

	public IntValue getValueCount() {
		return mValidValueCount;
	}

	public IntValue getRangeSize() {
		return mRangeSize;
	}

	public IntValue getMinimum() {
		return mMinimum;
	}

	public IntValue getMaximum() {
		return mMaximum;
	}

	@Override
	public String toString() {
		final StringBuilder inEqual = new StringBuilder();
		if (mInequal.size() > 0) {
			final Iterator<IntValue> iter = mInequal.iterator();
			inEqual.append(", n != {").append(iter.next());
			while (iter.hasNext()) {
				inEqual.append(", ").append(iter.next());
			}
			inEqual.append("}");
		}

		return (mMinimum == null ? "-infinity" : mMinimum) + " <= n <= " + (mMaximum == null ? "infinity" : mMaximum)
				+ inEqual.toString();
	}
}