package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter;

import java.math.BigInteger;

public class BitVector {
	/** The number of bits of the BitVector. */
	protected final int m;
	protected final BigInteger value;
	protected final BigInteger bitMask; // has 1 at every bit for the length first bits

	public BitVector(final int mLength, final BigInteger mValue) {
		assert mLength > 0;
		m = mLength;
		bitMask = BigInteger.ONE.shiftLeft(m).subtract(BigInteger.ONE);
		value = mValue.and(bitMask);
		assert value.compareTo(BigInteger.ZERO) >= 0;
	}

	protected static String pad(final String str, final int spaces, final char symbol) {
		final int unpadded = spaces - str.length();
		if (unpadded > 0) {
			return String.valueOf(symbol).repeat(unpadded) + str;
		}
		return str;
	}

	public String valueString() {
		final String fullString = value.toString(2);
		final int stringLength = fullString.length();
		if (m < stringLength) {
			return fullString.substring(stringLength - m);
		}
		return pad(fullString, m, '0');
	}

	public BitVector concat(final BitVector b) {
		return new BitVector(m + b.m, value.shiftLeft(m).add(b.value));
	}

	public BitVector extract(final int i, final int j) {
		assert m > i && i >= j && j >= 0;
		return new BitVector(i - j + 1, value.shiftRight(j));
	}

	/**
	 * bv2nat(b) := b[m-1]*2^{m-1} + b[m-2]*2^{m-2} + ⋯ + b[0]*2^0
	 */
	public BigInteger bv2nat() {
		final BigInteger out = BigInteger.ZERO;
		for (int i = 0; i < m; i++) {
			if (value.testBit(i)) {
				out.add(BigInteger.ONE.shiftLeft(i));
			}
		}
		return out;
	}

	/**
	 * bv2int(b) := if (b[m-1] = 1) then (bv2nat(b) - 2^m) else (bv2nat(b))
	 */
	public BigInteger bv2int() {
		if (value.testBit(m - 1)) {
			return bv2nat().subtract(BigInteger.ONE.shiftLeft(m));
		}
		return bv2nat();
	}

	/**
	 * b[m-1]*2^{m-1} + ⋯ + b[0]*2^0 = n mod 2^m
	 */
	@SuppressWarnings("static-method")
	public BitVector nat2bv(final int length, final BigInteger n) {
		assert length > 0 && n.compareTo(BigInteger.ZERO) >= 0;
		final BigInteger nMod2PowerM = n.mod(BigInteger.ONE.shiftLeft(length));

		// This does basically nothing except insuring that no bit above length can be known, set or unset.
		// If it can be proven correct, just return nMod2PowerM
		final BigInteger out = BigInteger.ZERO;
		for (int i = 0; i < length; i++) {
			if (nMod2PowerM.testBit(i)) {
				out.add(BigInteger.ONE.shiftLeft(i));
			}
		}
		return new BitVector(length, out);
	}

	/**
	 * b[m-1]*2^{m-1} + ⋯ + b[0]*2^0 = (n + 2^m) mod 2^m
	 */
	protected BitVector int2bv(final int length, final BigInteger n) {
		assert length > 0;
		return nat2bv(length, n.add(BigInteger.ONE.shiftLeft(length)));
	}

	public BitVector bvnot() {
		return new BitVector(m, value.not());
	}

	public BitVector bvand(final BitVector b) {
		assert m == b.m;
		return new BitVector(m, value.and(b.value));
	}

	public BitVector bvor(final BitVector b) {
		assert m == b.m;
		return new BitVector(m, value.or(b.value));
	}

	/**
	 * [[(bvneg s)]] := nat2bv[m](2^m - bv2nat([[s]]))
	 */
	public BitVector bvneg() {
		return nat2bv(m, BigInteger.ONE.shiftLeft(m).subtract(bv2nat()));
	}

	/**
	 * [[(bvadd s t)]] := nat2bv[m](bv2nat([[s]]) + bv2nat([[t]]))
	 */
	public BitVector bvadd(final BitVector t) {
		return nat2bv(m, bv2nat().add(t.bv2nat()));
	}

	/**
	 * [[(bvmul s t)]] := nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))
	 */
	public BitVector bvmul(final BitVector t) {
		return nat2bv(m, bv2nat().multiply(t.bv2nat()));
	}

	/**
	 * [[(bvudiv s t)]] := <br>
	 * <ul>
	 * if bv2nat([[t]]) = 0 <br>
	 * then λx:[0, m). 1 <br>
	 * else nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))
	 * </ul>
	 */
	public BitVector bvudiv(final BitVector t) {
		if (t.bv2nat().equals(BigInteger.ZERO)) {
			// returns BitVector of value 2^m-1, or 1 at all positions (max value)
			return new BitVector(m, BigInteger.ONE.shiftLeft(m).subtract(BigInteger.ONE));
		}
		return nat2bv(m, bv2nat().divide(t.bv2nat()));
	}

	/**
	 * [[(bvurem s t)]] := <br>
	 * <ul>
	 * if bv2nat([[t]]) = 0 <br>
	 * then [[s]] <br>
	 * else nat2bv[m](bv2nat([[s]]) mod bv2nat([[t]]))
	 * </ul>
	 */
	public BitVector bvurem(final BitVector t) {
		if (t.bv2nat().equals(BigInteger.ZERO)) {
			// returns self
			return this;
		}
		return nat2bv(m, bv2nat().remainder(t.bv2nat()));
	}

	protected static final BigInteger maxBigInt = BigInteger.valueOf(Integer.MAX_VALUE);

	/**
	 * [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
	 */
	public BitVector bvshl(final BitVector t) {
		final BigInteger shiftBy = t.bv2nat();
		if (maxBigInt.compareTo(shiftBy) < 0) {
			// shift by more than max length => all zero
			return new BitVector(m, BigInteger.ZERO);
		}
		return nat2bv(m, bv2nat().shiftLeft(shiftBy.intValue()));
	}

	/**
	 * [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
	 */
	public BitVector bvlshr(final BitVector t) {
		final BigInteger shiftBy = t.bv2nat();
		if (maxBigInt.compareTo(shiftBy) < 0) {
			// shift by more than max length => all zero
			return new BitVector(m, BigInteger.ZERO);
		}
		return nat2bv(m, bv2nat().shiftRight(shiftBy.intValue()));
	}

	/**
	 * [[bvult s t]] := true iff bv2nat([[s]]) < bv2nat([[t]])
	 */
	public boolean bvult(final BitVector t) {
		return bv2nat().compareTo(t.bv2nat()) < 0;
	}

	@Override
	public String toString() {
		return "BitVector[" + m + "] " + valueString();
	}

	@Override
	public boolean equals(final Object b) {
		if (!(b instanceof BitVector)) {
			return false;
		}
		final BitVector mBV = (BitVector) b;
		return m == mBV.m && value == mBV.value;
	}

	@SuppressWarnings("static-method")
	public BitVector newInstance(final int mLength, final BigInteger mValue) {
		return new BitVector(mLength, mValue);
	}

	/**
	 * Implementation that is less faithful to the SMT-LIB definitions.
	 */
	static class FastBitVector extends BitVector {
		public FastBitVector(final int mLength, final BigInteger mValue) {
			super(mLength, mValue);
		}

		@Override
		public BitVector concat(final BitVector b) {
			return new FastBitVector(m + b.m, value.shiftLeft(m).add(b.value));
		}

		@Override
		public BitVector extract(final int i, final int j) {
			assert m > i && i >= j && j >= 0;
			return new FastBitVector(i - j + 1, value.shiftRight(j));
		}

		@Override
		public FastBitVector bvnot() {
			return new FastBitVector(m, value.not());
		}

		@Override
		public FastBitVector bvand(final BitVector b) {
			assert m == b.m;
			return new FastBitVector(m, value.and(b.value));
		}

		@Override
		public FastBitVector bvor(final BitVector b) {
			assert m == b.m;
			return new FastBitVector(m, value.or(b.value));
		}

		@Override
		public FastBitVector bvneg() {
			return new FastBitVector(m, value.not().add(BigInteger.ONE));
		}

		@Override
		public FastBitVector bvadd(final BitVector t) {
			return new FastBitVector(m, value.add(t.value));
		}

		@Override
		public FastBitVector bvmul(final BitVector t) {
			return new FastBitVector(m, value.multiply(t.value));
		}

		@Override
		public FastBitVector bvudiv(final BitVector t) {
			if (t.value.equals(BigInteger.ZERO)) {
				return new FastBitVector(m, BigInteger.ONE.shiftLeft(m).subtract(BigInteger.ONE));
			}
			return new FastBitVector(m, value.divide(t.value));
		}

		@Override
		public FastBitVector bvurem(final BitVector t) {
			if (t.value.equals(BigInteger.ZERO)) {
				return this;
			}
			return new FastBitVector(m, value.remainder(t.value));
		}

		@Override
		public FastBitVector bvshl(final BitVector t) {
			final BigInteger shiftBy = t.bv2nat();
			if (maxBigInt.compareTo(shiftBy) < 0) {
				// shift by more than max length => all zero
				return new FastBitVector(m, BigInteger.ZERO);
			}
			return new FastBitVector(m, value.shiftLeft(t.value.intValue()));
		}

		@Override
		public FastBitVector bvlshr(final BitVector t) {
			final BigInteger shiftBy = t.bv2nat();
			if (maxBigInt.compareTo(shiftBy) < 0) {
				// shift by more than max length => all zero
				return new FastBitVector(m, BigInteger.ZERO);
			}
			return new FastBitVector(m, value.shiftRight(t.value.intValue()));
		}

		@Override
		public boolean bvult(final BitVector t) {
			return value.compareTo(t.value) < 0;
		}

		@Override
		public BitVector newInstance(final int mLength, final BigInteger mValue) {
			return new FastBitVector(mLength, mValue);
		}

		@Override
		public BitVector nat2bv(final int length, final BigInteger n) {
			assert length > 0 && n.compareTo(BigInteger.ZERO) >= 0;

			return new FastBitVector(length, n);
		}
	}
}
