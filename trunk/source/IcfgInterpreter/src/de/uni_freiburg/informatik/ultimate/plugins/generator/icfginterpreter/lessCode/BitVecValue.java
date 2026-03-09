package de.uni_freiburg.informatik.ultimate.plugins.generator.icfginterpreter.lessCode;

import java.math.BigInteger;
import java.util.Map;

import de.uni_freiburg.informatik.ultimate.logic.Rational;
import de.uni_freiburg.informatik.ultimate.logic.SMTLIBConstants;
import de.uni_freiburg.informatik.ultimate.logic.Script;
import de.uni_freiburg.informatik.ultimate.logic.Term;

public class BitVecValue implements Value {
	private final BigInteger mValue;
	/**
	 * The mask is used to ensure that the resulting BitVector is not negative / only has bits set to one up to the
	 * defined length.
	 */
	private final BigInteger mBitMask;
	private final int mLength;

	public BitVecValue(final BigInteger value, final int length) {
		mLength = length;
		mBitMask = BigInteger.ONE.shiftLeft(mLength).subtract(BigInteger.ONE);
		mValue = value.and(mBitMask);
	}

	// Assumes that the mask was applied to the value if necessary
	private BitVecValue(final BigInteger value, final BigInteger mask, final int length) {
		mLength = length;
		mBitMask = mask;
		mValue = value;
	}

	/**
	 * bv2nat(b) := b[m-1]*2^{m-1} + b[m-2]*2^{m-2} + ⋯ + b[0]*2^0
	 */
	public IntValue bv2nat() {
		// BitVector is "unsigned" thanks to the mask, the highest set bit can only be within the length first bits
		return new IntValue(mValue);
	}

	/**
	 * b[m-1]*2^{m-1} + ⋯ + b[0]*2^0 = n mod 2^m
	 */
	public BitVecValue nat2bv(final int length, final IntValue n) {
		return new BitVecValue(n.getValue(), length);
	}

	/**
	 * [[(concat s t)]] := λx:[0, n+m). if (x < m) then [[t]](x) else [[s]](x - m)
	 */
	public BitVecValue concat(final BitVecValue other) {
		final int newLength = mLength + other.mLength;
		assert newLength > 0;
		// (mValue << b.length) + b.mValue
		return new BitVecValue(mValue.shiftLeft(other.mLength).add(other.mValue), newLength);
	}

	/**
	 * [[((_ extract i j) s))]] := λx:[0, i-j+1). [[s]](j + x)
	 */
	public BitVecValue extract(final IntValue i, final IntValue j) {
		// Extracting bit mLength to j by shifting the value by j bits to the right.
		final BigInteger shifted = mValue.shiftRight(j.getValue().intValueExact());
		// The bits over the i-th one are automatically removed by the mask in the constructor
		final IntValue length = i.subtract(j).add(IntValue.ONE);
		return new BitVecValue(shifted, length.getValue().intValueExact());
	}

	/**
	 * [[(bvnot s)]] := λx:[0, m). if [[s]](x) = 0 then 1 else 0
	 */
	public BitVecValue bvnot() {
		return new BitVecValue(mValue.not(), mBitMask, mLength);
	}

	/**
	 * [[(bvneg s)]] := nat2bv[m](2^m - bv2nat([[s]]))
	 */
	public BitVecValue bvneg() {
		return nat2bv(mLength, new IntValue(BigInteger.ONE.shiftLeft(mLength).subtract(mValue)));
	}

	/**
	 * [[(bvand s t)]] := λx:[0, m). if [[s]](x) = 0 then 0 else [[t]](x)
	 */
	public BitVecValue bvand(final BitVecValue other) {
		return new BitVecValue(mValue.and(other.mValue), mBitMask, mLength);
	}

	/**
	 * [[(bvor s t)]] := λx:[0, m). if [[s]](x) = 1 then 1 else [[t]](x)
	 */
	public BitVecValue bvor(final BitVecValue other) {
		return new BitVecValue(mValue.or(other.mValue), mBitMask, mLength);
	}

	/**
	 * [[(bvadd s t)]] := nat2bv[m](bv2nat([[s]]) + bv2nat([[t]]))
	 */
	public BitVecValue bvadd(final BitVecValue other) {
		return nat2bv(mLength, bv2nat().add(other.bv2nat()));
	}

	/**
	 * [[(bvmul s t)]] := nat2bv[m](bv2nat([[s]]) * bv2nat([[t]]))
	 */
	public BitVecValue bvmul(final BitVecValue other) {
		return nat2bv(mLength, bv2nat().multiply(other.bv2nat()));
	}

	/**
	 * [[(bvudiv s t)]] :=
	 * <ul>
	 * if bv2nat([[t]]) = 0 <br>
	 * then λx:[0, m). 1 <br>
	 * else nat2bv[m](bv2nat([[s]]) div bv2nat([[t]]))
	 * </ul>
	 */
	public BitVecValue bvudiv(final BitVecValue other) {
		if (other.mValue.equals(BigInteger.ZERO)) {
			// returns BitVector of value 2^m-1, or 1 at all positions (max value)
			return new BitVecValue(BigInteger.ONE.shiftLeft(mLength).subtract(BigInteger.ONE), mLength);
		}
		return nat2bv(mLength, bv2nat().div(other.bv2nat()));
	}

	/**
	 * [[(bvurem s t)]] :=
	 * <ul>
	 * if bv2nat([[t]]) = 0 <br>
	 * then [[s]] <br>
	 * else nat2bv[m](bv2nat([[s]]) mod bv2nat([[t]]))
	 * </ul>
	 */
	public BitVecValue bvurem(final BitVecValue other) {
		if (other.mValue.equals(BigInteger.ZERO)) {
			// returns self
			return this;
		}
		return nat2bv(mLength, bv2nat().mod(other.bv2nat()));
	}

	/**
	 * [[(bvshl s t)]] := nat2bv[m](bv2nat([[s]]) * 2^(bv2nat([[t]])))
	 */
	public BitVecValue bvshl(final BitVecValue other) {
		final int length = other.mValue.intValueExact();
		final IntValue shiftBy = new IntValue(BigInteger.TWO.pow(length));

		return nat2bv(mLength, bv2nat().multiply(shiftBy));
	}

	/**
	 * [[(bvlshr s t)]] := nat2bv[m](bv2nat([[s]]) div 2^(bv2nat([[t]])))
	 */
	public BitVecValue bvlshr(final BitVecValue other) {
		final int length = other.mValue.intValueExact();
		final IntValue shiftBy = new IntValue(BigInteger.TWO.pow(length));

		return nat2bv(mLength, bv2nat().div(shiftBy));
	}

	/**
	 * [[bvult s t]] := true iff bv2nat([[s]]) < bv2nat([[t]])
	 */
	public BoolValue bvult(final BitVecValue other) {
		return bv2nat().lss(other.bv2nat());
	}

	@Override
	public BoolValue distinct(final Value other) {
		if (other instanceof final BitVecValue bvv) {
			return new BoolValue(!mValue.equals(bvv.mValue));
		}
		return BoolValue.mTrue;
	}

	@Override
	public BigInteger getValue() {
		return mValue;
	}

	@Override
	public String toString() {
		String out = mValue.toString(2);
		final int unpadded = mLength - out.length();
		if (unpadded > 0) {
			out = String.valueOf("0").repeat(unpadded) + out;
		}
		return "bv" + mLength + " " + out;
	}

	@Override
	public Map<Term, Term> toTerm(final Script script, final Term var) {
		return Map.of(var, script.getTheory().constant(Rational.valueOf(mValue, BigInteger.ONE),
				script.getTheory().getSort(SMTLIBConstants.BITVEC, new String[] { String.valueOf(mLength) })));
	}

	@Override
	public BoolValue equals(final Value other) {
		if (other instanceof final BitVecValue bvv) {
			return new BoolValue(mValue.equals(bvv.mValue));
		}
		return BoolValue.mFalse;
	}

	@Override
	public boolean equals(final Object b) {
		if (b instanceof final BitVecValue bvv) {
			return mValue.equals(bvv.mValue) && mLength == bvv.mLength;
		}
		return false;
	}

	@Override
	public int hashCode() {
		return mValue.hashCode();
	}

	@Override
	public int compareTo(final Value b) {
		if (b instanceof final BitVecValue bvv) {
			return mValue.compareTo(bvv.mValue);
		}
		return this.getClass().getSimpleName().compareTo(b.getClass().getSimpleName());
	}

	public int getLength() {
		return mLength;
	}
}