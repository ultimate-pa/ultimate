package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;
import java.util.function.BiPredicate;

public class IntegerRestriction extends Restriction<IntValue> {
	private final IntValue mValidValueCount;
	private final IntValue mRangeSize;

	public IntegerRestriction(final Set<IntValue> inequals, final IntValue minimum, final IntValue maximum) {
		super(inequals, minimum, maximum);
		if (mMinimum == null || mMaximum == null) {
			mRangeSize = null;
			mValidValueCount = null;
		} else {
			mRangeSize = mMaximum.subtract(mMinimum).add(IntValue.ONE); // number of values := max - min + 1
			mValidValueCount = mRangeSize.subtract(new IntValue(BigInteger.valueOf(mInequal.size())));

			if (mMinimum.compareTo(mMaximum) > 0 || IntValue.ZERO.compareTo(mValidValueCount) >= 0) {
				throw new EmptyRangeException();
			}
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
		if (!mInequal.isEmpty()) {
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

	/**
	 * If a is null, returns b and vice versa. <br>
	 * Otherwise, gets the first element if the comparator is true, the second if it is false.
	 *
	 * @return
	 */
	private static <T> T compareNull(final T a, final T b, final BiPredicate<T, T> comparator) {
		if (a != null && b != null) {
			return comparator.test(a, b) ? a : b;
		}

		return (a != null) ? a : b;
	}

	@Override
	public IntegerRestriction combine(final Restriction<?> other) {
		if (other instanceof final IntegerRestriction br) {

			final IntValue newMin = compareNull(mMinimum, br.mMinimum, (a, b) -> a.compareTo(b) >= 0);
			final IntValue newMax = compareNull(mMaximum, br.mMaximum, (a, b) -> a.compareTo(b) <= 0);

			final HashSet<IntValue> inEquals = new HashSet<>(mInequal);
			inEquals.addAll(br.mInequal);

			final HashSet<IntValue> cappedEquals = new HashSet<>();

			for (final IntValue inEqual : inEquals) {
				if ((newMin == null || newMin.compareTo(inEqual) <= 0)
						&& (newMax == null || inEqual.compareTo(newMax) <= 0)) {
					cappedEquals.add(inEqual);
				}
			}

			return new IntegerRestriction(cappedEquals, newMin, newMax);
		}
		return this;
	}
}