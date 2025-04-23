package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.HashSet;
import java.util.List;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Sort;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.BitVector;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.datatypes.SMTArray;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
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

		mHavocStandard = new IntegerRestriction(new HashSet<>(), mMinHavocInt, mMaxHavocInt);
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
	public long havocInt(IntegerRestriction values) {
		if (values == null) {
			values = mHavocStandard;
		}

		final long elementCount = values.getValueCount();
		final long index = (Math.abs(xorShift()) % elementCount);

		return values.getNthValue(index);
	}

	@Override
	public boolean havocBool(final BooleanRestriction values) {
		if (values != null && values.getInequal().size() == 1) {
			// can only be the value that is not in the inequalities
			return values.getInequal().contains(false);
		}
		// can be false or true (either both allowed or neither)
		return xorShift() < 0; // == is first bit 0 or 1
	}

	@Override
	public BitVector havocBitVector(final int length, final BitVectorRestriction values) {
		return new BitVector(length, BigInteger.ZERO);
	}

	@Override
	public SMTArray newArray(final Sort sort, final ArrayRestriction values) {
		return new SMTArray(sort);
	}

	@Override
	public Object havocArrayEntry(final SMTArray array, final Object index) {
		final long hashKey = array.hashCode() + index.hashCode();
		switch (array.mValueSort.getName()) {
		case SMTLIBConstants.ARRAY:
			return newArray(array.mValueSort, null);
		case SMTLIBConstants.BITVEC:
			return null;
		case SMTLIBConstants.BOOL:
			return 0 < hash(hashKey);
		case SMTLIBConstants.INT:
			return (Math.abs(hash(hashKey)) % mHavocStandard.getValueCount()) + mHavocStandard.getMinimum();
		}
		return null;
	}

	@Override
	public boolean areArraysEqual(final SMTArray a, final SMTArray b) {
		return havocBool(null);
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
	public static String MAX_INT_HAVOC_HINT =
			"Any value between Integer.MIN_VALUE and Integer.MAX_VALUE." + "\nHas to be more than the minimum option.";
	public static String MIN_INT_HAVOC_LABEL = "Minimum havoc integer value";
	public static String MIN_INT_HAVOC_HINT =
			"Any value between Integer.MIN_VALUE and Integer.MAX_VALUE." + "\nHas to be less than the maximum option.";
}
