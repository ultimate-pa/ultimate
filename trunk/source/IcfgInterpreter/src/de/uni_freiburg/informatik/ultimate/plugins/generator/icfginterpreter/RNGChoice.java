package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.ArrayList;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.BooleanDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain.Interval;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class RNGChoice implements NonDeterministicChoice {
	private int mSeed;

	public RNGChoice(final int seed) {
		mSeed = seed;
	}

	@Override
	public RNGChoice newInstance(final long seed) {
		return new RNGChoice((int) seed);
	}

	@Override
	public <T> T chooseEdge(final ArrayList<T> edges) {
		return edges.get((int) chooseElement(edges.size()));
	}

	@Override
	public int havocInt(final VariableIntegerTerm variable, final IntegerDomain values) {
		long index = chooseElement(values.getValueCount());

		final ArrayList<Interval> intervals = values.getValues();

		for (final Interval interval : intervals) {
			final float containedValues = interval.getValueCount();

			if (containedValues >= index) {
				return interval.getMin() + (int) index;
			}

			index -= containedValues;
		}

		assert false;
		return 0;
	}

	@Override
	public boolean havocBool(final VariableBooleanTerm variable, final BooleanDomain values) {
		if (values.isEmpty()) {
			assert false;
			return false;
		}
		if (values.getValueCount() == 1) {
			// can either only be true or only be false
			return values.canBeTrue;
		}
		// can be false or true
		return xorShift() < 0; // == is first bit 0 or 1
	}

	@Override
	public BitVector havocBitVector(final Variable variable, final Domain<?> values) {
		return null;
	}

	@Override
	public SMTArray newArray(final VariableArrayTerm variable, final ArrayDomain<?, ?> values) {
		return new SMTArray(variable.keyType, variable.valueType, variable);
	}

	@Override
	public Object havocArrayEntry(final SMTArray array, final Object index) {
		final long hashKey = array.variable.getVariableTerm().programVar.hashCode() + index.hashCode();
		switch (array.valueType) {
		case Array:
			return newArray(array.variable, (ArrayDomain<?, ?>) array.variable.getDomain());
		case BitVector:
			return havocBitVector(null, null);

		case Boolean:
			return 0 < hash(hashKey);
		case Int:
			return hash(hashKey);
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
}