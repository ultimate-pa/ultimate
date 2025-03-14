package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashMap;

import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.ArrayDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.BooleanDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.Domain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.domains.IntegerDomain;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.array.VariableArrayTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.bool.VariableBooleanTerm;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.generic.Variable;
import de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.terms.integer.VariableIntegerTerm;

public class RNGChoice implements NonDeterministicChoice {
	private int seed;

	public RNGChoice(final int mSeed) {
		seed = mSeed;
	}

	@Override
	public RNGChoice newInstance(final long mSeed) {
		return new RNGChoice((int) mSeed);
	}

	@Override
	public <T> T chooseEdge(final ArrayList<T> edges) {
		final int index = Math.abs(havocInt(null, null)) % edges.size();
		return edges.get(index);
	}

	@Override
	public int havocInt(final VariableIntegerTerm variable, final IntegerDomain values) {
		return xorShift();
	}

	@Override
	public boolean havocBool(final VariableBooleanTerm variable, final BooleanDomain values) {
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
			return newArray(array.variable, new ArrayDomain<>(new HashMap<>(), array.keyType, array.valueType));
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

	private int xorShift() {
		seed = xorShift(seed);
		return seed;
	}
}