package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.ArrayValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BitVecValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.BoolValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.IntValue;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode.Value;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;

public class RNGChoice implements NonDeterministicChoice {
	private long mSeed;
	private IntegerRestriction mHavocStandard;

	public RNGChoice() {
		// non-instance constructor that will be used to create actual instances with specific seeds
	}

	public RNGChoice(final long seed) throws Exception {
		mSeed = seed;

		final RcpPreferenceProvider settings = IcfgInterpreterPreferences.getPreferences();
		long mMaxHavocInt = settings.getInt(MAX_INT_HAVOC_LABEL, Integer.MAX_VALUE);
		long mMinHavocInt = settings.getInt(MIN_INT_HAVOC_LABEL, Integer.MIN_VALUE + 1);
		if (mMaxHavocInt < mMinHavocInt) {
			// Settings are the wrong way around
			final long swap = mMaxHavocInt;
			mMaxHavocInt = mMinHavocInt;
			mMinHavocInt = swap;

			settings.put(MAX_INT_HAVOC_HINT, mMaxHavocInt);
			settings.put(MIN_INT_HAVOC_LABEL, mMinHavocInt);
			throw new Exception("Wrong settings for " + IcfgInterpreter.class.getSimpleName()
					+ ", maximum havoc value is less than the minimum havoc value");
		}

		mHavocStandard = new IntegerRestriction(new HashSet<>(), new IntValue(BigInteger.valueOf(mMinHavocInt)),
				new IntValue(BigInteger.valueOf(mMaxHavocInt)));
	}

	private RNGChoice(final long seed, final IntegerRestriction havocStandard) {
		// constructor used for quick cloning
		mSeed = seed;
		mHavocStandard = havocStandard;
	}

	@Override
	public RNGChoice newInstance(final long seed) {
		try {
			return new RNGChoice(seed);
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public <T> T chooseEdge(final List<T> edges) {
		return edges.get((int) chooseElement(edges.size()));
	}

	@Override
	public IntValue havocInt(IntegerRestriction values) {
		if (values == null) {
			values = mHavocStandard;
		}

		if (values.getValueCount() == null) {
			// one or both ends are unlimited

			IntValue value = null;
			while (value == null || values.getInequal().contains(value)) {
				value = new IntValue(BigInteger.valueOf(xorShift()));
				// cap the value should either end be finite
				if ((values.getMaximum() != null) && (values.getMaximum().compareTo(value) < 0)) {
					value = values.getMaximum().subtract(value.abs());
				} else if ((values.getMinimum() != null) && (value.compareTo(values.getMinimum()) < 0)) {
					value = values.getMinimum().add(value.abs());
				}
			}

			return value;
		}

		// the range has finite bounds
		final IntValue index = new IntValue(BigInteger.valueOf(Math.abs(xorShift()))).mod(values.getValueCount());

		IntValue currentValue = values.getMinimum().add(index);
		IntValue skipped = IntValue.ZERO;
		boolean contained = values.getInequal().contains(currentValue);

		while (contained || IntValue.ZERO.compareTo(skipped) < 0) {
			if (!contained) {
				skipped = skipped.subtract(IntValue.ONE);
			} else {
				skipped = skipped.add(IntValue.ONE);
			}
			currentValue = currentValue.add(IntValue.ONE);
			if (values.getMaximum().compareTo(currentValue) <= 0) {
				currentValue = currentValue.subtract(values.getRangeSize());
			}
			contained = values.getInequal().contains(currentValue);
		}
		assert values.getMinimum().compareTo(currentValue) <= 0 && currentValue.compareTo(values.getMaximum()) <= 0;
		return currentValue;
	}

	@Override
	public BoolValue havocBool(final BooleanRestriction values) {
		if (values != null && values.getInequal().size() == 1) {
			// can only be the value that is not in the inequalities
			return new BoolValue(values.getInequal().contains(BoolValue.mFalse));
		}
		// can be false or true (either both allowed or neither)
		return new BoolValue(xorShift() < 0); // == is first bit 0 or 1
	}

	@Override
	public BitVecValue havocBitVector(final int length, final BitVectorRestriction values) {
		return new BitVecValue(BigInteger.ZERO, length);
	}

	@Override
	public ArrayValue newArray(final Sort sort, final String uniqueIdentifier, final ArrayRestriction values) {
		return new ArrayValue(new HashMap<>(), uniqueIdentifier, sort);
	}

	@Override
	public Value havocArrayEntry(final ArrayValue array, final Value index) {
		final long hashKey = array.hashCode() + index.hashCode();
		switch (array.getSort().getArguments()[0].getName()) {
		case SMTLIBConstants.ARRAY:
			return newArray(array.getSort().getArguments()[1], array.getUniqueIdentifier() + " _ " + index, null);
		case SMTLIBConstants.BITVEC:
			return null;
		case SMTLIBConstants.BOOL:
			return new BoolValue(0 < hash(hashKey));
		case SMTLIBConstants.INT:
			final IntValue value = new IntValue(BigInteger.valueOf(Math.abs(hash(hashKey))));
			return value.mod(mHavocStandard.getValueCount()).add(mHavocStandard.getMinimum());
		}
		return null;
	}

	/** http://zimbry.blogspot.com/2011/09/better-bit-mixing-improving-on.html */
	public static long hash(long seed) {
		seed = (seed ^ (seed >>> 30)) * 0xbf58476d1ce4e5b9L;
		seed = (seed ^ (seed >>> 27)) * 0x94d049bb133111ebL;
		seed ^= (seed >>> 31);
		return seed;
	}

	public static long xorShift(long seed) {
		seed ^= seed << 13;
		seed ^= seed >> 17;
		seed ^= seed << 5;
		return seed;
	}

	private long chooseElement(final long size) {
		return Math.abs(xorShift()) % size;
	}

	private long xorShift() {
		mSeed = xorShift(mSeed);
		return mSeed;
	}

	@Override
	public UltimatePreferenceItemGroup getImplementationSettings() {
		return new UltimatePreferenceItemGroup(getClass().getSimpleName(),
				new UltimatePreferenceItem<>(MAX_INT_HAVOC_LABEL, Integer.MAX_VALUE, MAX_INT_HAVOC_HINT,
						PreferenceType.Integer),
				new UltimatePreferenceItem<>(MIN_INT_HAVOC_LABEL, Integer.MIN_VALUE, MIN_INT_HAVOC_HINT,
						PreferenceType.Integer));
	}

	@Override
	public RNGChoice clone() {
		return new RNGChoice(mSeed, mHavocStandard);
	}

	public static String MAX_INT_HAVOC_LABEL = "Maximum havoc integer value";
	public static String MAX_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be more than the minimum option.";
	public static String MIN_INT_HAVOC_LABEL = "Minimum havoc integer value";
	public static String MIN_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be less than the maximum option.";
}
