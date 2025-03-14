package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains;

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.function.BiFunction;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.Util;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.ExecutionTerm.ReturnType;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.IntegerTerm;

public class IntegerDomain implements Domain<IntegerDomain> {
	private final ArrayList<Interval> possibleValues;

	public IntegerDomain() {
		possibleValues = new ArrayList<>();
	}

	public IntegerDomain(final Interval mPossibleValues) {
		possibleValues = new ArrayList<>();
		possibleValues.add(mPossibleValues);
	}

	public IntegerDomain(final ArrayList<Interval> mPossibleValues) {
		possibleValues = unionize(mPossibleValues);
	}

	@Override
	public ArrayList<Interval> getValues() {
		return Util.copyList(possibleValues);
	}

	public int size() {
		return possibleValues.size();
	}

	@Override
	public IntegerDomain intersection(final IntegerDomain domain) {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				final Interval intervalC = Interval.intersection(intervalA, intervalB);
				if (intervalC == null) {
					continue;
				}
				newValues.add(intervalC);
			}
		}

		return new IntegerDomain(newValues);
	}

	@Override
	public IntegerDomain difference(final IntegerDomain domain) {
		final IntegerDomain notInA = domain.complement(this);
		final IntegerDomain notInB = complement(domain);

		return notInA.union(notInB);
	}

	@Override
	public IntegerDomain union(final IntegerDomain domain) {
		final ArrayList<Interval> result = new ArrayList<>(possibleValues);

		result.addAll(domain.possibleValues);

		return new IntegerDomain(result);
	}

	@Override
	public IntegerDomain complement(final IntegerDomain domain) {
		ArrayList<Interval> newValues = Util.copyList(possibleValues);

		for (final Interval intervalExcluded : domain.possibleValues) {
			final ArrayList<Interval> tempValues = new ArrayList<>();
			for (final Interval interval : newValues) {
				final Interval[] reducedIntervals = Interval.complement(interval, intervalExcluded);
				Collections.addAll(tempValues, reducedIntervals);
			}
			newValues = tempValues;
		}

		return new IntegerDomain(newValues);
	}

	@Override
	public boolean contains(final Domain<?> domain) {
		if (!(domain instanceof IntegerDomain)) {
			return false;
		}
		return ((IntegerDomain) domain).complement(this).isEmpty();
	}

	/**
	 * Reduces this {@link IntegerDomain} such that all remaining values are also in the given Interval
	 *
	 * @param domain
	 * @return
	 */
	public IntegerDomain intersect(final Interval interval) {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval intervalA : possibleValues) {
			final Interval intervalC = Interval.intersection(intervalA, interval);
			if (intervalC == null) {
				continue;
			}
			newValues.add(intervalC);
		}

		return new IntegerDomain(newValues);
	}

	public IntegerDomain absoluteOf() {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval intervalA : possibleValues) {
			Interval interval;
			if (intervalA.min < 0 && 0 < intervalA.max) {
				// min is below zero, max is above abs([-17, 5]) => [0, 17]
				final int max = Math.max(Math.abs(intervalA.min), intervalA.max);
				interval = new Interval(0, max);

			} else if (intervalA.min < 0) {
				// both below 0 abs([-17, -5]) => [5, 17]
				interval = new Interval(-intervalA.max, -intervalA.min);
			} else {
				// interval already positive
				interval = intervalA;
			}

			newValues.add(interval);
		}

		return new IntegerDomain(newValues);
	}

	public IntegerDomain addition(final IntegerDomain domain) {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				newValues.add(Interval.addition(intervalA, intervalB));
			}
		}

		return new IntegerDomain(newValues);
	}

	/**
	 * Algebraically multiply the given domain to this one.
	 *
	 * @param domain
	 */
	public IntegerDomain multiply(final IntegerDomain domain) {
		IntegerDomain result = new IntegerDomain();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				result = result.union(Interval.multiplication(intervalA, intervalB));
			}
		}

		return result;
	}

	/**
	 * Algebraically subtract the given domain from this one.
	 *
	 * @param domain
	 */
	public IntegerDomain subtract(final IntegerDomain domain) {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				newValues.add(Interval.subtraction(intervalA, intervalB));
			}
		}

		return new IntegerDomain(newValues);
	}

	/**
	 * Algebraically get the domain of values that can occur when dividing any value of this domain by any from the
	 * given domain.
	 *
	 * @param domain
	 */
	public IntegerDomain divide(final IntegerDomain domain) {
		IntegerDomain result = new IntegerDomain();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				result = result.union(Interval.division(intervalA, intervalB));
			}
		}

		return result;
	}

	/**
	 * Algebraically get the domain of values that can occur when modulating any value of this domain by any from the
	 * given domain.
	 *
	 * @param domain
	 */
	public IntegerDomain remainder(final IntegerDomain domain) {
		IntegerDomain result = new IntegerDomain();

		for (final Interval intervalA : possibleValues) {
			for (final Interval intervalB : domain.possibleValues) {
				result = result.union(Interval.remainder(intervalA, intervalB));
			}
		}

		return result;
	}

	/**
	 * Flips values on the number axis; [-15, 34] => [-34, 15]
	 *
	 * @param domain
	 */
	public IntegerDomain negate() {
		final ArrayList<Interval> newValues = new ArrayList<>();

		for (final Interval interval : possibleValues) {
			newValues.add(interval.negate());
		}

		return new IntegerDomain(newValues);
	}

	public Interval getMinimum() {
		return possibleValues.get(0);
	}

	public Interval getMaximum() {
		return possibleValues.get(possibleValues.size() - 1);
	}

	private static void sort(final ArrayList<Interval> values) {
		values.sort(Comparator.comparing(a -> a.min));
	}

	/**
	 * The variable defined by this domain is less then the max value of <strong>domain</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain lessThen(final IntegerDomain domain) {
		if (domain.isEmpty()) {
			// all values already less than any of domain
			return this;
		}
		// return the intersection of this domain and the interval [minimumInt, domain.highestValue - 1]
		int max = domain.getMaximum().max;
		if (max > Interval.MIN) {
			max--;
		}
		return intersect(new Interval(null, max));
	}

	/**
	 * The variable defined by this domain is less or equal to the max value of <strong>domain</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain lessEqual(final IntegerDomain domain) {
		if (domain.isEmpty()) {
			// all values already less than any of domain
			return this;
		}
		// return the intersection of this domain and the interval [minimumInt, domain.highestValue]
		return intersect(new Interval(null, domain.getMaximum().max));
	}

	/**
	 * Apply constraint, the variable defined by this domain is greater then <strong>term</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain greaterThen(final IntegerDomain domain) {
		if (domain.isEmpty()) {
			// all values already less than any of domain
			return this;
		}
		// return the intersection of this domain and the interval [domain.lowestValue + 1, maximumInt]
		int min = domain.getMinimum().min;
		if (min < Interval.MAX) {
			min++;
		}
		return intersect(new Interval(min, null));
	}

	/**
	 * Apply constraint, the variable defined by this domain is greater or equal to <strong>term</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain greaterEqual(final IntegerDomain domain) {
		if (domain.isEmpty()) {
			// all values already less than any of domain
			return this;
		}
		// return the intersection of this domain and the interval [domain.lowestValue, maximumInt]
		return intersect(new Interval(domain.getMinimum().min, null));
	}

	/**
	 * Apply constraint, the variable defined by this domain is equal to <strong>term</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain equals(final IntegerDomain domain) {
		return intersection(domain);
	}

	/**
	 * Apply constraint, the variable defined by this domain is not equal to <strong>term</strong>
	 *
	 * @param term {@link IntegerTerm} that contains no {@link Variables}
	 */
	public IntegerDomain unequal(final IntegerDomain domain) {
		return complement(domain);
	}

	/**
	 * Merges overlapping and adjacent Intervals
	 *
	 * @param intervals
	 * @return
	 */
	public static ArrayList<Interval> unionize(final ArrayList<Interval> intervals) {
		if (intervals.size() == 0) {
			return intervals;
		}

		final ArrayList<Interval> result = Util.copyList(intervals);
		boolean unchanged = false;
		while (!unchanged) {
			unchanged = true;
			for (int i = 0; i < result.size() && unchanged; i++) {
				final Interval current = result.get(i);
				for (int j = 0; j < result.size(); j++) {
					if (i == j) {
						continue;
					}
					final Interval other = result.get(j);
					if (current.overlaps(other) || current.adjacent(other)) {
						result.remove(current);
						result.remove(other);
						result.add(Interval.union(current, other));
						unchanged = false;
						break;
					}
				}
			}
		}

		sort(result);

		return result;
	}

	@Override
	public String toString() {
		final String[] intervalStrings = new String[possibleValues.size()];
		for (int i = 0; i < possibleValues.size(); i++) {
			intervalStrings[i] = possibleValues.get(i).toString();
		}
		return "{" + String.join(", ", intervalStrings) + "}";
	}

	@Override
	public boolean isEmpty() {
		return possibleValues.size() == 0;
	}

	@Override
	public ReturnType getType() {
		return ReturnType.Int;
	}

	@Override
	public IntegerDomain getFullDomain() {
		return new IntegerDomain(new Interval(null, null));
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof IntegerDomain)) {
			return false;
		}
		final IntegerDomain bCast = (IntegerDomain) b;
		return possibleValues.equals(bCast.possibleValues);
	}

	@Override
	public IntegerDomain domainFrom(final Object singleValue) {
		if (!(singleValue instanceof Integer)) {
			return new IntegerDomain();
		}
		final int value = (int) singleValue;
		return new IntegerDomain(new Interval(value, value));
	}

	public static class Interval {
		private final int min;
		private final int max;
		public static final int MAX = Integer.MAX_VALUE;
		public static final int MIN = Integer.MIN_VALUE + 1;

		public Interval() {
			this(null, null);
		}

		public Interval(Integer mMin, Integer mMax) {
			if (mMin == null) {
				mMin = MIN;
			}
			if (mMax == null) {
				mMax = MAX;
			}
			assert mMin <= mMax;
			min = mMin;
			max = mMax;
		}

		public boolean includes(final int a) {
			return min <= a && a <= max;
		}

		public boolean overlaps(final Interval b) {
			return min <= b.max && b.min <= max;
		}

		public boolean contains(final Interval b) {
			return min <= b.min && b.max <= max;
		}

		public boolean adjacent(final Interval b) {
			return (MIN < min && min - 1 == b.max) || (max < MAX && max + 1 == b.min);
		}

		public static Interval intersection(final Interval a, final Interval b) {
			if (!a.overlaps(b)) {
				return null;
			}
			final int minValue = (a.min < b.min) ? b.min : a.min;
			final int maxValue = (a.max < b.max) ? a.max : b.max;

			return new Interval(minValue, maxValue);
		}

		public static Interval union(final Interval a, final Interval b) {
			if (!a.overlaps(b) && !a.adjacent(b)) {
				return null;
			}
			final int minValue = (a.min < b.min) ? a.min : b.min;
			final int maxValue = (a.max < b.max) ? b.max : a.max;

			return new Interval(minValue, maxValue);
		}

		/** Intervals that contain all values of A that are not in B */
		public static Interval[] complement(final Interval a, final Interval b) {
			final ArrayList<Interval> out = new ArrayList<>();

			if (!a.overlaps(b)) {
				out.add(a);
			} else {
				if (a.min < b.min) {
					out.add(new Interval(a.min, b.min - 1));
				}
				if (b.max < a.max) {
					out.add(new Interval(b.max + 1, a.max));
				}
			}

			return out.toArray(new Interval[out.size()]);
		}

		private static Interval arithmatic(final Interval a, final Interval b,
				final BiFunction<Long, Long, Long> operation) {
			final long aMin = a.min;
			final long bMin = b.min;
			final long aMax = a.max;
			final long bMax = b.max;

			final long[] values = { capValue(operation.apply(aMin, bMin)), capValue(operation.apply(aMax, bMin)),
					capValue(operation.apply(aMin, bMax)), capValue(operation.apply(aMax, bMax)) };

			long min = MAX + 1L;
			long max = MIN - 1L;
			for (int i = 0; i < 4; i++) {
				// cap values to prevent integer over / underflow
				final long current = capValue(values[i]);

				if (current > max) {
					max = (int) current;
				}
				if (current < min) {
					min = (int) current;
				} else {
					continue;
				}
			}

			return new Interval((int) min, (int) max);
		}

		private static long capValue(final long value) {
			if (value > MAX) {
				return MAX;
			}
			if (value < MIN) {
				return MIN;
			}
			return value;
		}

		public static Interval addition(final Interval a, final Interval b) {
			return arithmatic(a, b, (m, n) -> {
				return m + n;
			});
		}

		public static IntegerDomain multiplication(final Interval a, final Interval b) {
			return new IntegerDomain(arithmatic(a, b, (m, n) -> {
				return m * n;
			}));

			// [x, ..., y] * [a, ..., b] => [x*a, x*b] + [(x+1)*a, (x+1)*b] + ... + [y*a, ..., y*b]
			// sum(x<=i<=y, [i*a, i*b])
			/*
			 * ArrayList<Interval> result = new ArrayList<>(); for(int i = a.min; i <= a.max; i++) { int r1 = (int)
			 * capValue(i * b.min); int r2 = (int) capValue(i * b.max); result.add(new Interval(Math.min(r1, r2),
			 * Math.max(r1, r2))); }
			 *
			 *
			 * return new IntegerDomain(result);
			 */
		}

		public static Interval subtraction(final Interval a, final Interval b) {
			return arithmatic(a, b, (m, n) -> {
				return m - n;
			});
		}

		private static Interval avoidDiv = new Interval(-1, 1);

		public static IntegerDomain division(final Interval a, final Interval b) {
			IntegerDomain result = new IntegerDomain();

			final Interval[] bSafe = complement(b, avoidDiv); // b without [-1,0,1]

			for (final Interval interval : bSafe) {
				result = result.union(divisionInternal(a, interval));
			}

			// specific cases of a / 1 (identity) and a / 0 (error)
			if (b.overlaps(avoidDiv)) {
				final IntegerDomain aDom = new IntegerDomain(a);
				result = result.union(aDom).union(aDom.negate()); // add a and -a
			}

			return result;
		}

		// ignores -1, 0, and 1
		private static IntegerDomain divisionInternal(final Interval a, final Interval b) {
			if (0 < b.min) {
				// b is positive
				if (0 < a.min) {
					// a is positive
					// [3, 6] / [2, 4] => 3 / 4, 6 / 2 => [0, 3]
					// int minA = a.min == 1 ? 2 : a.min;
					final int min = Util.SMTDiv(a.min, b.max);
					final int max = Util.SMTDiv(a.max, b.min);
					return new IntegerDomain(new Interval(min, max));
				} else if (a.max < 0) {
					// a is negative
					// [-6, -4] / [2, 4] => -6 / 2, -4 / 4 => [-3, -1]
					// int maxA = a.max == -1 ? -2 : a.max;
					final int min = Util.SMTDiv(a.min, b.min);
					final int max = Util.SMTDiv(a.max, b.max);
					return new IntegerDomain(new Interval(min, max));
				}
				// a includes 0
				// [-3, 6] / [2, 4] => -3 / 2, 6 / 2 => [-1, 3]
				// [-6, 3] / [2, 4] => -6 / 2, 3 / 2 => [-3, 1]

				final Interval[] aSplit = complement(a, new Interval(0, 0)); // split into above and below, add back 0
																				// at end
				IntegerDomain result = new IntegerDomain();
				for (final Interval split : aSplit) {
					result = result.union(divisionInternal(split, b));
				}

				return result.union(new IntegerDomain(new Interval(0, 0)));
				/*
				 * int min = DivisionTerm.SMTDiv(a.min, b.min); int max = DivisionTerm.SMTDiv(a.max, b.min); return new
				 * IntegerDomain(removeNonDiv(new Interval(min, max), a, b));
				 */
			} else if (b.max < 0) {
				// b is negative
				if (0 < a.min) {
					// a is positive
					// [3, 6] / [-4, -2] => 6 / -2, 3 / -4 => [-3, 0]
					// int minA = a.min == 1 ? 2 : a.min;
					final int min = Util.SMTDiv(a.max, b.max);
					final int max = Util.SMTDiv(a.min, b.min);
					return new IntegerDomain(new Interval(min, max));
				} else if (a.max < 0) {
					// a is negative
					// [-6, -4] / [-4, -2] => -4 / -4, -6 / -2 => [1, 3]
					// int maxA = a.max == -1 ? -2 : a.max;
					final int min = Util.SMTDiv(a.max, b.min);
					final int max = Util.SMTDiv(a.min, b.max);
					return new IntegerDomain(new Interval(min, max));
				}
				// a includes 0
				// [-3, 6] / [-4, -2] => 6 / -2, -3 / -2 => [-3, 1]
				// [-6, 3] / [-4, -2] => 3 / -2, -6 / -2 => [-1, 3]
				final Interval[] aSplit = complement(a, new Interval(0, 0)); // split into above and below, add back 0
																				// at end
				IntegerDomain result = new IntegerDomain();
				for (final Interval split : aSplit) {
					result = result.union(divisionInternal(split, b));
				}

				return result.union(new IntegerDomain(new Interval(0, 0)));

				/*
				 * int min = DivisionTerm.SMTDiv(a.max, b.max); int max = DivisionTerm.SMTDiv(a.min, b.max); return new
				 * IntegerDomain(removeNonDiv(new Interval(min, max), a, b));
				 */
			}
			// b includes 0
			// cut into intervals [b.min, -1] [1, b.max], then divide each normally
			IntegerDomain lowerDivision = null;
			IntegerDomain higherDivision = null;
			int foundIntervals = 0;
			if (b.min < -1) {
				// remaining interval is at least [-1, -1]
				lowerDivision = divisionInternal(a, new Interval(b.min, -2));
				foundIntervals++;
			}
			if (b.max > 1) {
				// remaining interval is at least [1, 1]
				higherDivision = divisionInternal(a, new Interval(2, b.max));
				foundIntervals++;
			}

			final IntegerDomain[] out = new IntegerDomain[foundIntervals];

			if (higherDivision != null) {
				foundIntervals--;
				out[foundIntervals] = higherDivision;
			}
			if (lowerDivision != null) {
				foundIntervals--;
				out[foundIntervals] = lowerDivision;
			}

			if (out.length == 1) {
				return out[0];
			}
			if (out.length == 0) {
				return new IntegerDomain(new ArrayList<>());
			}

			return out[0].union(out[1]);
		}

		public static IntegerDomain remainder(final Interval a, final Interval b) {
			final IntegerDomain divided = division(a, b); // a / b
			final IntegerDomain multiplied = divided.multiply(new IntegerDomain(b)); // (a / b) * b
			return new IntegerDomain(a).subtract(multiplied); // a mod b := a - ((a / b) * b);
		}

		public Interval negate() {
			return new Interval(-max, -min);
		}

		@Override
		public String toString() {
			String out;
			if (max == min) {
				out = String.valueOf(min);
			} else if (max == min + 1) {
				out = min + ", " + max;
			} else {
				out = min + ", ..., " + max;
			}
			return "[" + out + "]";
		}

		@Override
		public boolean equals(final Object b) {
			if (!(b instanceof Interval)) {
				return false;
			}
			final Interval castB = (Interval) b;
			return min == castB.min && max == castB.max;
		}

		public final int getMax() {
			return max;
		}

		public final int getMin() {
			return min;
		}
	}
}
