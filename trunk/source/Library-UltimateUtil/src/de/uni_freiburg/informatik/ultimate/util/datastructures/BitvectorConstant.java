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

	public enum SupportedBitvectorOperations {
		zero_extend, extract, bvadd, bvsub, bvmul, bvudiv, bvurem, bvsdiv, bvsrem, bvand, bvor, bvxor, bvnot, bvneg,
		bvshl, bvlshr, bvashr, bvult, bvule, bvugt, bvuge, bvslt, bvsle, bvsgt, bvsge,
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

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((mIndex == null) ? 0 : mIndex.hashCode());
		result = prime * result + ((mValue == null) ? 0 : mValue.hashCode());
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

}
