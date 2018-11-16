/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 *
 * This file is part of the ULTIMATE ModelCheckerUtils Library.
 *
 * The ULTIMATE ModelCheckerUtils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE ModelCheckerUtils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE ModelCheckerUtils Library. If not, see <http://www.gnu.org/licenses/>.
 *
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE ModelCheckerUtils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP),
 * containing parts covered by the terms of the Eclipse Public License, the
 * licensors of the ULTIMATE ModelCheckerUtils Library grant you additional permission
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util.datastructures;

import java.math.BigInteger;
import java.util.function.Function;

/**
 * Representation of bitvectors.
 *
 * @author Matthias Heizmann
 *
 */
public class BitvectorConstant {

	/**
	 * Describes bitvector operations that can be mapped to the SMT theory of fixed-size bitvectors
	 * (http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml or http://smtlib.cs.uiowa.edu/logics-all.shtml).
	 *
	 * @author Matthias Heizmann
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public enum SupportedBitvectorOperations {
		/**
		 * ((_ zero_extend i) x)
		 *
		 * extend x with zeroes to the (unsigned) equivalent bitvector of size m+i
		 */
		zero_extend(2, false, false),

		/**
		 * ((_ extract i j) (_ BitVec m) (_ BitVec n))
		 *
		 * extraction of bits i down to j from a bitvector of size m to yield a new bitvector of size n, where n = i - j
		 * + 1
		 */
		extract(3, false, false),

		/**
		 * (bvadd (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * addition modulo 2^m
		 */
		bvadd(2, false, true),

		/**
		 * (bvsub (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * 2's complement subtraction modulo 2^m
		 */
		bvsub(2, false, false),

		/**
		 * (bvmul (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * multiplication modulo 2^m
		 */
		bvmul(2, false, true),

		/**
		 * (bvudiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * unsigned division, truncating towards 0
		 */
		bvudiv(2, false, false),

		/**
		 * (bvurem (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * unsigned remainder from truncating division
		 */
		bvurem(2, false, false),

		/**
		 * (bvsdiv (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * 2's complement signed division
		 */
		bvsdiv(2, false, false),

		/**
		 * (bvsrem (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * 2's complement signed remainder (sign follows dividend)
		 */
		bvsrem(2, false, false),

		/**
		 * (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * bitwise and
		 */
		bvand(2, false, true),

		/**
		 * (bvor (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * bitwise or
		 */
		bvor(2, false, true),

		/**
		 * (bvxor (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * bitwise exclusive or
		 */
		bvxor(2, false, true),

		/**
		 * (bvnot (_ BitVec m) (_ BitVec m))
		 *
		 * bitwise negation
		 */
		bvnot(1, false, true),

		/**
		 * (bvneg (_ BitVec m) (_ BitVec m))
		 *
		 * 2's complement unary minus
		 */
		bvneg(1, false, true),

		/**
		 * (bvshl (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * shift left (equivalent to multiplication by 2^x where x is the value of the second argument)
		 */
		bvshl(2, false, false),

		/**
		 * (bvlshr (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * logical shift right (equivalent to unsigned division by 2^x where x is the value of the second argument)
		 */
		bvlshr(2, false, false),

		/**
		 * (bvashr (_ BitVec m) (_ BitVec m) (_ BitVec m))
		 *
		 * Arithmetic shift right, like logical shift right except that the most significant bits of the result always
		 * copy the most significant bit of the first argument.
		 */
		bvashr(2, false, false),

		/**
		 * (bvult (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for unsigned less-than
		 */
		bvult(2, true, false),

		/**
		 * (bvule (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for unsigned less than or equal
		 */
		bvule(2, true, false),

		/**
		 * (bvugt (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for unsigned greater than
		 */
		bvugt(2, true, false),

		/**
		 * (bvuge (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for unsigned greater than or equal
		 */
		bvuge(2, true, false),

		/**
		 * (bvslt (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for signed less than
		 */
		bvslt(2, true, false),

		/**
		 * (bvsle (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for signed less than or equal
		 */
		bvsle(2, true, false),

		/**
		 * (bvsgt (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for signed greater than
		 */
		bvsgt(2, true, false),

		/**
		 * (bvsge (_ BitVec m) (_ BitVec m) Bool)
		 *
		 * binary predicate for signed greater than or equal
		 */
		bvsge(2, true, false);

		private final int mArity;
		private final boolean mIsBoolean;
		private final boolean mIsAssociative;

		private SupportedBitvectorOperations(final int arity, final boolean isBoolean, final boolean isAssoc) {
			mArity = arity;
			mIsBoolean = isBoolean;
			mIsAssociative = isAssoc;
		}

		/**
		 * @return the arity of this operation
		 */
		public int getArity() {
			return mArity;
		}

		/**
		 * @return true iff the result of this operation is of type boolean, false otherwise
		 */
		public boolean isBoolean() {
			return mIsBoolean;
		}

		/**
		 * @return true iff the order of the operands does not matter.
		 */
		public boolean isCommutative() {
			return mIsAssociative;
		}

	}

	private final BigInteger mValue;
	private final BigInteger mIndex;

	public BitvectorConstant(final BigInteger value, final BigInteger index) {
		super();
		mValue = computeUnifiedValue(value, index);
		mIndex = index;
	}

	/**
	 * @return the result of value % 2^index
	 */
	private static BigInteger computeUnifiedValue(final BigInteger value, final BigInteger index) {
		return value.mod(new BigInteger("2").pow(index.intValueExact()));
	}

	public BigInteger getValue() {
		return mValue;
	}

	public BigInteger getIndex() {
		return mIndex;
	}

	public boolean isZero() {
		return mValue.signum() == 0;
	}

	public boolean isOne() {
		return mValue.equals(BigInteger.ONE);
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mIndex == null ? 0 : mIndex.hashCode());
		result = prime * result + (mValue == null ? 0 : mValue.hashCode());
		return result;
	}

	@Override
	public boolean equals(final Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		final BitvectorConstant other = (BitvectorConstant) obj;
		if (mIndex == null) {
			if (other.mIndex != null) {
				return false;
			}
		} else if (!mIndex.equals(other.mIndex)) {
			return false;
		}
		if (mValue == null) {
			if (other.mValue != null) {
				return false;
			}
		} else if (!mValue.equals(other.mValue)) {
			return false;
		}
		return true;
	}

	/**
	 * returns the numeral SMT-LIB representation of this bitvector constant
	 */
	@Override
	public String toString() {
		return "(_ bv" + mValue + " " + mIndex + ")";
	}

	public static BitvectorConstant maxValue(final int index) {
		return new BitvectorConstant(BigInteger.valueOf(2).pow(index).subtract(BigInteger.valueOf(1)),
				BigInteger.valueOf(index));
	}

	public static BitvectorConstant maxValue(final BigInteger index) {
		return new BitvectorConstant(BigInteger.valueOf(2).pow(index.intValueExact()).subtract(BigInteger.valueOf(1)),
				index);
	}

	public static BitvectorConstant bvadd(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.add(y));
	}

	public static BitvectorConstant bvsub(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.subtract(y));
	}

	public static BitvectorConstant bvmul(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.multiply(y));
	}

	public static BitvectorConstant bvudiv(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.divide(y));
	}

	public static BitvectorConstant bvurem(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.remainder(y));
	}

	public static BitvectorConstant bvsdiv(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).divide(toSignedInt(y, bv2.getIndex())));
	}

	public static BitvectorConstant bvsrem(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).remainder(toSignedInt(y, bv2.getIndex())));
	}

	public static BitvectorConstant bvand(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.and(y));
	}

	public static BitvectorConstant bvor(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.or(y));
	}

	public static BitvectorConstant bvxor(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.xor(y));
	}

	public static BitvectorConstant bvshl(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.shiftLeft(y.intValueExact()));
	}

	public static BitvectorConstant bvlshr(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2, x -> y -> x.shiftRight(y.intValueExact()));
	}

	public static BitvectorConstant bvashr(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return similarIndexBvOp_BitvectorResult(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).shiftRight(y.intValueExact()));
	}

	public static BitvectorConstant bvnot(final BitvectorConstant bv) {
		return new BitvectorConstant(bv.getValue().not(), bv.getIndex());
	}

	public static BitvectorConstant bvneg(final BitvectorConstant bv) {
		return new BitvectorConstant(toSignedInt(bv.getValue(), bv.getIndex()).negate(), bv.getIndex());
	}

	public static BitvectorConstant similarIndexBvOp_BitvectorResult(final BitvectorConstant bv1,
			final BitvectorConstant bv2, final Function<BigInteger, Function<BigInteger, BigInteger>> fun) {
		if (bv1.getIndex().equals(bv2.getIndex())) {
			return new BitvectorConstant(fun.apply(bv1.getValue()).apply(bv2.getValue()), bv1.getIndex());
		}
		throw new IllegalArgumentException("incompatible indices " + bv1.getIndex() + " " + bv2.getIndex());
	}

	public static Boolean comparison(final BitvectorConstant bv1, final BitvectorConstant bv2,
			final Function<BigInteger, Function<BigInteger, Boolean>> fun) {
		if (bv1.getIndex().equals(bv2.getIndex())) {
			return fun.apply(bv1.getValue()).apply(bv2.getValue());
		}
		throw new IllegalArgumentException("incompatible indices " + bv1.getIndex() + " " + bv2.getIndex());
	}

	// public static BitvectorConstant bvshl(BitvectorConstant b1, BitvectorConstant b2) {
	// int effectiveShift = Math.min(b1.getIndex().intValueExact(), b2.getValue().intValue());
	// return new BitvectorConstant(b1.getValue().multiply(new BigInteger("2").pow(effectiveShift)), b1.getIndex());
	// }

	public static boolean bvult(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2, x -> y -> x.compareTo(y) < 0);
	}

	public static boolean bvule(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2, x -> y -> x.compareTo(y) <= 0);
	}

	public static boolean bvugt(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2, x -> y -> x.compareTo(y) > 0);
	}

	public static boolean bvuge(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2, x -> y -> x.compareTo(y) >= 0);
	}

	public static boolean bvslt(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).compareTo(toSignedInt(y, bv2.getIndex())) < 0);
	}

	public static boolean bvsle(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).compareTo(toSignedInt(y, bv2.getIndex())) <= 0);
	}

	public static boolean bvsgt(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).compareTo(toSignedInt(y, bv2.getIndex())) > 0);
	}

	public static boolean bvsge(final BitvectorConstant bv1, final BitvectorConstant bv2) {
		return comparison(bv1, bv2,
				x -> y -> toSignedInt(x, bv1.getIndex()).compareTo(toSignedInt(y, bv2.getIndex())) >= 0);
	}

	public static BitvectorConstant extract(final BitvectorConstant bv, final int upperIndex, final int lowerIndex) {
		final String binaryString = bvToBinaryString(bv);
		final int resultIndex = upperIndex + 1 - lowerIndex;
		final String extractedBinaryString;
		if (resultIndex < binaryString.length()) {
			extractedBinaryString =
					binaryString.substring(binaryString.length() - 1 - upperIndex, binaryString.length() - lowerIndex);
		} else {
			extractedBinaryString = binaryString;
		}
		final BigInteger extractedValue = binaryStringToBv(extractedBinaryString);
		return new BitvectorConstant(extractedValue, BigInteger.valueOf(resultIndex));
	}

	private static BigInteger binaryStringToBv(final String extractedBinaryString) {
		return new BigInteger(extractedBinaryString, 2);
	}

	private static String bvToBinaryString(final BitvectorConstant bv) {
		final String number = bv.getValue().toString(2);
		final String leadingZeros =
				new String(new char[bv.getIndex().intValueExact() - number.length()]).replace('\0', '0');
		final String result = leadingZeros + number;
		assert result.length() == bv.getIndex().intValueExact();
		return result;
	}

	public static BitvectorConstant zero_extend(final BitvectorConstant bv, final BigInteger index) {
		return new BitvectorConstant(bv.getValue(), bv.getIndex().add(index));
	}

	public static BigInteger toSignedInt(final BigInteger bvValue, final BigInteger bvIndex) {
		final BigInteger firstNegative = new BigInteger("2").pow(bvIndex.intValueExact() - 1);
		if (bvValue.compareTo(firstNegative) < 0) {
			return bvValue;
		}
		final BigInteger biggestUnsigned = new BigInteger("2").pow(bvIndex.intValueExact());
		return bvValue.subtract(biggestUnsigned);
	}

	public BigInteger toSignedInt() {
		return toSignedInt(mValue, mIndex);
	}

	public static BitvectorConstantOperationResult apply(final SupportedBitvectorOperations sbo,
			final BitvectorConstant... operands) {
		if (operands == null) {
			throw new IllegalArgumentException("No operands");
		}
		if (operands.length != sbo.getArity()) {
			throw new IllegalArgumentException("Operation " + sbo + " has arity " + sbo.getArity() + " but "
					+ operands.length + " operands given");
		}
		switch (sbo) {
		case bvadd:
			return new BitvectorConstantOperationResult(bvadd(operands[0], operands[1]));
		case bvand:
			return new BitvectorConstantOperationResult(bvand(operands[0], operands[1]));
		case bvashr:
			return new BitvectorConstantOperationResult(bvashr(operands[0], operands[1]));
		case bvlshr:
			return new BitvectorConstantOperationResult(bvlshr(operands[0], operands[1]));
		case bvmul:
			return new BitvectorConstantOperationResult(bvmul(operands[0], operands[1]));
		case bvneg:
			return new BitvectorConstantOperationResult(bvneg(operands[0]));
		case bvnot:
			return new BitvectorConstantOperationResult(bvnot(operands[0]));
		case bvor:
			return new BitvectorConstantOperationResult(bvor(operands[0], operands[1]));
		case bvsdiv:
			return new BitvectorConstantOperationResult(bvsdiv(operands[0], operands[1]));
		case bvsge:
			return new BitvectorConstantOperationResult(bvsge(operands[0], operands[1]));
		case bvsgt:
			return new BitvectorConstantOperationResult(bvsgt(operands[0], operands[1]));
		case bvshl:
			return new BitvectorConstantOperationResult(bvshl(operands[0], operands[1]));
		case bvsle:
			return new BitvectorConstantOperationResult(bvsle(operands[0], operands[1]));
		case bvslt:
			return new BitvectorConstantOperationResult(bvslt(operands[0], operands[1]));
		case bvsrem:
			return new BitvectorConstantOperationResult(bvsrem(operands[0], operands[1]));
		case bvsub:
			return new BitvectorConstantOperationResult(bvsub(operands[0], operands[1]));
		case bvudiv:
			return new BitvectorConstantOperationResult(bvudiv(operands[0], operands[1]));
		case bvuge:
			return new BitvectorConstantOperationResult(bvuge(operands[0], operands[1]));
		case bvugt:
			return new BitvectorConstantOperationResult(bvugt(operands[0], operands[1]));
		case bvule:
			return new BitvectorConstantOperationResult(bvule(operands[0], operands[1]));
		case bvult:
			return new BitvectorConstantOperationResult(bvult(operands[0], operands[1]));
		case bvurem:
			return new BitvectorConstantOperationResult(bvurem(operands[0], operands[1]));
		case bvxor:
			return new BitvectorConstantOperationResult(bvxor(operands[0], operands[1]));
		default:
			throw new UnsupportedOperationException("Operation currently unsupported: " + sbo);
		}
	}

	/**
	 *
	 * @author Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
	 *
	 */
	public static final class BitvectorConstantOperationResult {

		private final BitvectorConstant mBvResult;
		private final Boolean mBooleanResult;

		public BitvectorConstantOperationResult(final BitvectorConstant result) {
			mBvResult = result;
			mBooleanResult = null;
		}

		public BitvectorConstantOperationResult(final boolean result) {
			mBvResult = null;
			mBooleanResult = result;
		}

		public boolean isBoolean() {
			return mBooleanResult != null;
		}

		public boolean getBooleanResult() {
			return mBooleanResult.booleanValue();
		}

		public BitvectorConstant getBvResult() {
			return mBvResult;
		}
	}

}
