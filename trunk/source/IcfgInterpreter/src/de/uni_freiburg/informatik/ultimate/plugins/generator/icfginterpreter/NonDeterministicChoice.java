package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.List;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.lib.smtlibutils.SmtSortUtils;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.BitVecValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datastructures.Value;

/**
 * This class should be deterministic for its seed. This ensures that the same "non-deterministic" values appear when
 * the same key is given, allowing users to isolate a specific case and recreate it later.<br>
 * There should be a constructor for this class that has no parameters. An instance created this way will be used to
 * make the instances that will actually be used via {@link #newInstance(long)}
 */
public class NonDeterministicChoice {
	private final Random mRandom;
	private final IntValue mMin;
	private final IntValue mMax;

	public NonDeterministicChoice(final long seed, final int minBits, final int maxBits) {
		mRandom = new Random(seed);
		mMin = new IntValue(BigInteger.TWO.pow(minBits).negate().add(BigInteger.ONE));
		mMax = new IntValue(BigInteger.TWO.pow(maxBits).subtract(BigInteger.ONE));
	}

	public <T> T chooseEdge(final List<T> edges) {
		return edges.get(mRandom.nextInt(0, edges.size()));
	}

	/**
	 * Select a non-deterministic value in the range defined by the domain for the given variable.
	 *
	 * @param possibleValues
	 * @return
	 */
	public Value havoc(final Sort sort, final Restriction<?> possibleValues) {
		switch (sort.getName()) {
		case SMTLIBConstants.ARRAY:
			throw new AssertionError("Arrays can not be havoced.");
		case SMTLIBConstants.INT:
			return havocInt((IntegerRestriction) possibleValues);
		case SMTLIBConstants.BITVEC:
			final int length = SmtSortUtils.getBitvectorLength(sort);
			return havocBitVector(length, (IntegerRestriction) possibleValues);
		case SMTLIBConstants.BOOL:
			return havocBool((BooleanRestriction) possibleValues);
		default:
			return null;
		}
	}

	private static IntegerRestriction boundIntRestriction(final IntegerRestriction values, final IntValue minInt,
			final IntValue maxInt) {
		IntValue min;
		IntValue max;
		Set<IntValue> inequal;

		if (values == null) {
			inequal = Set.of();
			min = minInt;
			max = maxInt;
		} else {
			inequal = values.getInequal();

			min = values.getMinimum();
			max = values.getMaximum();
			if (min == null) {
				min = minInt;
			}
			if (max == null) {
				max = maxInt;
			}
		}

		return new IntegerRestriction(inequal, min, max);
	}

	public IntValue havocInt(final IntegerRestriction values) {
		final IntegerRestriction boundedValues = boundIntRestriction(values, mMin, mMax);

		final int length = boundedValues.getRangeSize().getValue().subtract(BigInteger.ONE).bitLength();

		return havocInt(boundedValues, length);
	}

	public BitVecValue havocBitVector(final int length, final IntegerRestriction values) {
		final IntValue min = new IntValue(BigInteger.TWO.pow(length - 1).negate());
		final IntValue max = new IntValue(BigInteger.TWO.pow(length - 1));
		final IntegerRestriction boundedValues = boundIntRestriction(values, min, max);

		return new BitVecValue(havocInt(boundedValues, length).getValue(), length);
	}

	/**
	 * Generates a random BigInteger from [0, maximum).
	 *
	 * @param length
	 *            The number of bits, optimally this is maximum.bitLength()
	 * @param maximum
	 *            The random value generated is at most maximum - 1.
	 * @return
	 */
	private BigInteger randomBigInt(final int length, final BigInteger maximum) {
		BigInteger randBigInt = new BigInteger(length, mRandom);
		while (randBigInt.compareTo(maximum) >= 0) {
			randBigInt = new BigInteger(length, mRandom);
		}
		return randBigInt;
	}

	private IntValue havocInt(final IntegerRestriction values, final int length) {
		final IntValue minimum = values.getMinimum();
		final BigInteger valueCount = values.getRangeSize().getValue();
		IntValue randIntVal = new IntValue(randomBigInt(length, valueCount)).add(minimum);

		while (values.getInequal().contains(randIntVal)) {
			randIntVal = new IntValue(randomBigInt(length, valueCount)).add(minimum);
		}

		if (randIntVal.lss(minimum).getValue() || values.getMaximum().lss(randIntVal).getValue()) {
			return randIntVal;
		}

		return randIntVal;
	}

	public BoolValue havocBool(final BooleanRestriction values) {
		if (values != null && values.getInequal().size() == 1) {
			// can only be the value that is not in the inequalities
			return new BoolValue(values.getInequal().contains(BoolValue.FALSE));
		}
		// can be false or true (either both allowed or neither)
		return new BoolValue(mRandom.nextBoolean());
	}
}
