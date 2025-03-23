package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.core.model.preferences.PreferenceType;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItem;
import de.uni_freiburg.informatik.ultimate.core.model.preferences.UltimatePreferenceItemGroup;
import de.uni_freiburg.informatik.ultimate.core.preferences.RcpPreferenceProvider;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.ArrayRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BitVectorRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.BooleanRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.interpret.IntegerRestriction;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.preferences.IcfgInterpreterPreferences;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bitvector.VariableBitVectorTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class RNGChoice implements NonDeterministicChoice {
	private int mSeed;
	private int mMinHavocInt;
	private int mHavocCapMap;

	public RNGChoice() {
		// non-instance constructor that will be used to create actual instances with specific seeds
	}

	public RNGChoice(final int seed) throws Exception {
		mSeed = seed;

		final RcpPreferenceProvider settings = IcfgInterpreterPreferences.getPreferences();
		final int mMaxHavocInt = settings.getInt(MAX_INT_HAVOC_LABEL, Integer.MAX_VALUE);
		mMinHavocInt = settings.getInt(MIN_INT_HAVOC_LABEL, Integer.MIN_VALUE + 1);
		mHavocCapMap = mMaxHavocInt - mMinHavocInt + 1;
		if (mMaxHavocInt < mMinHavocInt) {
			throw new Exception("Wrong settings for " + IcfgInterpreter.class.getSimpleName()
					+ ", maximum havoc value is less than the minimum havoc value");
		}
	}

	@Override
	public RNGChoice newInstance(final long seed) {
		try {
			return new RNGChoice((int) seed);
		} catch (final Exception e) {
			e.printStackTrace();
		}
		return null;
	}

	@Override
	public <T> T chooseEdge(final ArrayList<T> edges) {
		return edges.get((int) chooseElement(edges.size()));
	}

	@Override
	public int havocInt(final VariableIntegerTerm variable, final IntegerRestriction values) {
		if (values == null) {
			return (Math.abs(xorShift()) % mHavocCapMap) + mMinHavocInt;
		}

		final int index = (Math.abs(xorShift()) % values.getValueCount());
		int value = values.getLess() + 1 + index;
		while (values.getInequal().contains(value)) {
			value++;
		}

		return value;
	}

	@Override
	public boolean havocBool(final VariableBooleanTerm variable, final BooleanRestriction values) {
		if (values != null && values.getInequal().size() == 1) {
			// can only be the value that is not in the inequalities
			return values.getInequal().contains(false);
		}
		// can be false or true (either both allowed or neither)
		return xorShift() < 0; // == is first bit 0 or 1
	}

	@Override
	public BitVector havocBitVector(final VariableBitVectorTerm variable, final BitVectorRestriction values) {
		return null;
	}

	@Override
	public SMTArray newArray(final VariableArrayTerm variable, final ArrayRestriction values) {
		return new SMTArray(variable.keyType, variable.valueType, variable);
	}

	@Override
	public Object havocArrayEntry(final SMTArray array, final Object index) {
		final long hashKey = array.variable.getVariableTerm().programVar.hashCode() + index.hashCode();
		switch (array.valueType) {
		case Array:
			return newArray(array.variable, null);
		case BitVector:
			return null;
		case Boolean:
			return 0 < hash(hashKey);
		case Int:
			return (Math.abs((int) hash(hashKey)) % mHavocCapMap) + mMinHavocInt;
		}
		return null;
	}

	@Override
	public boolean areArraysEqual(final SMTArray a, final SMTArray b) {
		return havocBool(null, null);
	}

	/** 0xbf58476d1ce4e5b9L */
	private static final BigInteger par1 = BigInteger.valueOf(1378784879315654392L).multiply(BigInteger.valueOf(10))
			.add(BigInteger.valueOf(9));
	/** 0x94d049bb133111ebL */
	private static final BigInteger par2 = BigInteger.valueOf(1072315178059884593L).multiply(BigInteger.valueOf(10))
			.add(BigInteger.valueOf(1));
	/** 0xffffffffffffffffL */
	private static final BigInteger cap = BigInteger.valueOf(Long.MAX_VALUE).shiftLeft(1).add(BigInteger.ONE);

	public static long hash(BigInteger seed) {
		seed = seed.xor(seed.shiftRight(30)).multiply(par1).and(cap);
		seed = seed.xor(seed.shiftRight(27)).multiply(par2).and(cap);
		seed = seed.xor(seed.shiftRight(31));
		return seed.longValue();
	}

	/** http://zimbry.blogspot.com/2011/09/better-bit-mixing-improving-on.html */
	public static long hash(long seed) {
		// return hashB(BigInteger.valueOf(seed));
		seed = (seed ^ (seed >>> 30)) * 0xbf58476d1ce4e5b9L;
		seed = (seed ^ (seed >>> 27)) * 0x94d049bb133111ebL;
		seed ^= (seed >>> 31);
		return seed;
	}

	public static int xorShift(int seed) {
		seed ^= seed << 13;
		seed ^= seed >> 17;
		seed ^= seed << 5;
		return seed;
	}

	private long chooseElement(final long size) {
		return Math.abs(xorShift()) % size;
	}

	private int xorShift() {
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

	public static String MAX_INT_HAVOC_LABEL = "Maximum havoc integer value";
	public static String MAX_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be more than the minimum option.";
	public static String MIN_INT_HAVOC_LABEL = "Minimum havoc integer value";
	public static String MIN_INT_HAVOC_HINT = "Any value between Integer.MIN_VALUE and Integer.MAX_VALUE."
			+ "\nHas to be less than the maximum option.";
}