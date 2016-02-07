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
package de.uni_freiburg.informatik.ultimate.modelcheckerutils.smt;

import java.math.BigInteger;
import java.util.function.Function;

/**
 * Representation of bitvectors.
 * @author Matthias Heizmann
 *
 */
public class BitvectorConstant {
	private final BigInteger m_Value;
	private final BigInteger m_Index;
	
	
	public BitvectorConstant(BigInteger value, BigInteger index) {
		super();
		m_Value = computeUnifiedValue(value, index);
		m_Index = index;
	}
	
	
	/**
	 * @return the result of value % 2^index
	 */
	private BigInteger computeUnifiedValue(BigInteger value, BigInteger index) {
		return value.mod(new BigInteger("2").pow(index.intValueExact()));
	}

	public BigInteger getValue() {
		return m_Value;
	}

	public BigInteger getIndex() {
		return m_Index;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((m_Index == null) ? 0 : m_Index.hashCode());
		result = prime * result + ((m_Value == null) ? 0 : m_Value.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		BitvectorConstant other = (BitvectorConstant) obj;
		if (m_Index == null) {
			if (other.m_Index != null)
				return false;
		} else if (!m_Index.equals(other.m_Index))
			return false;
		if (m_Value == null) {
			if (other.m_Value != null)
				return false;
		} else if (!m_Value.equals(other.m_Value))
			return false;
		return true;
	}

	/**
	 * returns the numeral SMT-LIB representation of this bitvector constant
	 */
	@Override
	public String toString() {
		return "(_ bv" + m_Value + " " + m_Index + ")";
	}
	
	
	
	public static BitvectorConstant bvadd(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.add(y));
	}
	
	public static BitvectorConstant bvsub(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.subtract(y));
	}
	
	public static BitvectorConstant bvmul(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.multiply(y));
	}
	
	public static BitvectorConstant bvand(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.and(y));
	}
	
	public static BitvectorConstant bvor(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.or(y));
	}
	
	public static BitvectorConstant bxor(BitvectorConstant bv1, BitvectorConstant bv2) {
		return similarIndexBvOp(bv1, bv2, x -> y -> x.xor(y));
	}

	
	public static BitvectorConstant similarIndexBvOp(BitvectorConstant bv1, BitvectorConstant bv2, Function<BigInteger, Function<BigInteger, BigInteger>> fun) {
		if (bv1.getIndex().equals(bv2.getIndex())) {
			return new BitvectorConstant(fun.apply(bv1.getValue()).apply(bv2.getValue()), bv1.getIndex());
		} else {
			throw new IllegalArgumentException("incompatible indices " + bv1.getIndex() + " " + bv2.getIndex());
		}
	}
	
	
	public static BitvectorConstant bvshl(BitvectorConstant b1, BitvectorConstant b2) {
		int effectiveShift = Math.min(b1.getIndex().intValueExact(), b2.getValue().intValue());
		return new BitvectorConstant(b1.getValue().multiply(new BigInteger("2").pow(effectiveShift)), b1.getIndex());
	}
	
	public static boolean bvult(BitvectorConstant b1, BitvectorConstant b2) {
		if (b1.getIndex().equals(b2.getIndex())) {
			return b1.getValue().compareTo(b2.getValue()) < 0;
		} else {
			throw new IllegalArgumentException("incompatible indices " + b1.getIndex() + " " + b2.getIndex());
		}
	}

	public static BitvectorConstant extract(BitvectorConstant bv, int upperIndex, int lowerIndex) {
		String binaryString = bvToBinaryString(bv);
		int resultIndex = upperIndex + 1 - lowerIndex;
		final String extractedBinaryString;
		if (resultIndex < binaryString.length()) {
			extractedBinaryString = binaryString.substring(
					binaryString.length()-1-upperIndex, binaryString.length()-lowerIndex);
		} else {
			extractedBinaryString = binaryString;
		}
		BigInteger extractedValue = binaryStringToBv(extractedBinaryString);
		return new BitvectorConstant(extractedValue, BigInteger.valueOf(resultIndex));
	}


	private static BigInteger binaryStringToBv(final String extractedBinaryString) {
		return new BigInteger(extractedBinaryString, 2);
	}


	private static String bvToBinaryString(BitvectorConstant bv) {
		return bv.getValue().toString(2);
	}
	
	private static String bvToFullBinaryString(BitvectorConstant bv) {
		String withoutZeros = bv.getValue().toString(2);
		StringBuilder sb = new StringBuilder();
		int missingZeros = bv.getIndex().intValueExact() - withoutZeros.length(); 
		for (int i=0; i<missingZeros; i++) {
			sb.append("0");
		}
		sb.append(withoutZeros);
		return sb.toString();
	}



	public static BitvectorConstant zero_extend(BitvectorConstant bv, BigInteger index) {
		return new BitvectorConstant(bv.getValue(), bv.getIndex().add(index));
	}

	
	
}
