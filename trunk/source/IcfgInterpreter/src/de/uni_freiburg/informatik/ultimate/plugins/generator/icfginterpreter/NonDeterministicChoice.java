package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.List;
import java.util.Random;
import java.util.Set;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.Restriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BitVecValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;

/**
 * This class should be deterministic for its seed. This ensures that the same "non-deterministic" values appear when
 * the same key is given, allowing users to isolate a specific case and recreate it later.<br>
 * There should be a constructor for this class that has no parameters. An instance created this way will be used to
 * make the instances that will actually be used via {@link #newInstance(long)}
 */
public class NonDeterministicChoice {
	private final Random mRandom;
	private final int mHavocBits;

	public NonDeterministicChoice(final long seed, final int havocBits) {
		mRandom = new Random(seed);
		mHavocBits = havocBits;
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
			final int length = Util.getBitVecLength(sort);
			return havocBitVector(length, (IntegerRestriction) possibleValues);
		case SMTLIBConstants.BOOL:
			return havocBool((BooleanRestriction) possibleValues);
		default:
			return null;
		}
	}

	public IntValue havocInt(final IntegerRestriction values) {
		final int length = mRandom.nextInt(2, mHavocBits);
		return havocInt(values, length);
	}

	private IntValue havocInt(final IntegerRestriction values, final int length) {
		IntValue randBigInt = new IntValue(new BigInteger(length, mRandom));

		// Make sure that negative numbers can appear
		if (mRandom.nextBoolean()) {
			randBigInt = randBigInt.negate();
		}

		if (values == null) {
			return randBigInt;
		}

		final IntValue minimum = values.getMinimum();
		final IntValue maximum = values.getMaximum();
		final IntValue valueCount = values.getValueCount();
		final Set<IntValue> inEqual = values.getInequal();

		if (minimum == null) {
			if (maximum != null && randBigInt.compareTo(maximum) > 0) {
				randBigInt = maximum.subtract(randBigInt.subtract(maximum).abs());
			}
		} else {
			if (maximum == null) {
				if (randBigInt.compareTo(minimum) < 0) {
					randBigInt = minimum.add(minimum.subtract(randBigInt).abs());
				}
			} else {
				randBigInt = randBigInt.abs().mod(valueCount).add(minimum);
			}
		}

		while (inEqual.contains(randBigInt)) {
			randBigInt = randBigInt.add(IntValue.ONE);
			if (maximum != null && randBigInt.compareTo(maximum) >= 0) {
				randBigInt = minimum;
			}
		}
		return randBigInt;
	}

	public BoolValue havocBool(final BooleanRestriction values) {
		if (values != null && values.getInequal().size() == 1) {
			// can only be the value that is not in the inequalities
			return new BoolValue(values.getInequal().contains(BoolValue.mFalse));
		}
		// can be false or true (either both allowed or neither)
		return new BoolValue(mRandom.nextBoolean());
	}

	public BitVecValue havocBitVector(final int length, final IntegerRestriction values) {
		return new BitVecValue(havocInt(values, length).getValue(), length);
	}

	public UltimatePreferenceItemGroup getImplementationSettings() {
		return new UltimatePreferenceItemGroup(getClass().getSimpleName(),
				new UltimatePreferenceItem<>(MAX_INT_HAVOC_LABEL, Integer.MAX_VALUE, MAX_INT_HAVOC_HINT,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(MIN_INT_HAVOC_LABEL, Integer.MIN_VALUE, MIN_INT_HAVOC_HINT,
						PreferenceType.Integer));
	}

	public static String MAX_INT_HAVOC_LABEL = "Maximum havoc integer value";
	public static String MAX_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be more than the minimum option.";
	public static String MIN_INT_HAVOC_LABEL = "Minimum havoc integer value";
	public static String MIN_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be less than the maximum option.";
}
