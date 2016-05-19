/*
 * Copyright (C) 2014-2015 Alexander Nutz (nutz@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Daniel Dietsch (dietsch@informatik.uni-freiburg.de)
 * Copyright (C) 2015 Markus Lindenmann (lindenmm@informatik.uni-freiburg.de)
 * Copyright (C) 2013-2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE CACSL2BoogieTranslator plug-in.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE CACSL2BoogieTranslator plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE CACSL2BoogieTranslator plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE CACSL2BoogieTranslator plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE CACSL2BoogieTranslator plug-in grant you additional permission 
 * to convey the resulting work.
 */
/**
 * Methods, helping to interpret C constants.
 */
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util;

import java.math.BigDecimal;
import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation;
import de.uni_freiburg.informatik.ultimate.boogie.DeclarationInformation.StorageClass;
import de.uni_freiburg.informatik.ultimate.boogie.ast.BitvecLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.FunctionApplication;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IdentifierExpression;
import de.uni_freiburg.informatik.ultimate.boogie.ast.IntegerLiteral;
import de.uni_freiburg.informatik.ultimate.boogie.ast.RealLiteral;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.FunctionDeclarations;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.cHandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.PRIMITIVE;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CType;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.UnsupportedSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;

/**
 * This class holds methods, that help translating constants.
 * 
 * @author Markus Lindenmann
 * @date 12.07.2012
 */
public final class ISOIEC9899TC3 {
	/**
	 * Message: "Ignored suffix".
	 */
	private static final String IGNORED_SUFFIX = "Ignored suffix";
	/**
	 * Octal prefix.
	 */
	private static final String OCT_0 = SFO.NR0;
	/**
	 * HEX lower case prefix.
	 */
	private static final String HEX_U0X = "0X";
	/**
	 * HEX upper case prefix.
	 */
	private static final String HEX_L0X = "0x";
	/**
	 * Float suffixes.
	 */
	private static final String[] SUFFIXES_FLOAT = new String[] { "f", "F", "l", "L" };
	/**
	 * Integer suffixes.
	 */
	private static final String[] SUFFIXES_INT = new String[] { "ULL", "Ull", "ull", "uLL", "llu", "llU", "LLu", "LLU",
			"ul", "uL", "Ul", "UL", "lu", "lU", "Lu", "LU", "ll", "LL", "u", "U", "l", "L" };
	
	public enum IntegerConstantType {
		OCTAL(8), 
		DECIMAL(10), 
		HEXADECIMAL(16);
		
		private final int m_Base;
		IntegerConstantType(int base) {
			m_Base = base;
		}
		
		public int getBase() {
			return m_Base;
		}
	}

	/**
	 * Parses Integer constants according to <a
	 * href="www.open-std.org/jtc1/sc22/WG14/www/docs/n1256.pdf">ISO/IEC
	 * 9899:TC3</a>, chapter 6.4.4.4.
	 * 
	 * @param val
	 *            the value to parse
	 * @param loc
	 *            the location
	 * @return the parsed value
	 */
	public static final String handleCharConstant(String val, ILocation loc, Dispatcher dispatch) {
		int value;
		if (val.startsWith("L")) {
			// ignore wide character prefix
			val = val.substring(1, val.length());
			String msg = IGNORED_SUFFIX + "Char-Sequence wide character suffix L dropped";
			dispatch.warn(loc, msg);
		}
		if (!val.startsWith("'") || !val.endsWith("'")) {
			throw new UnsupportedOperationException();
		}

		if (val.charAt(1) == '\\') {
			switch (val.charAt(2)) {
			case '\'':
			case '\"':
			case '?':
			case '\\':
				value = (int) val.charAt(2);
				break;
			case 'a':
				value = 7;
				break;
			case 'b':
				value = 8;
				break;
			case 'f':
				value = 12;
				break;
			case 'n':
				value = 10;
				break;
			case 'r':
				value = 13;
				break;
			case 't':
				value = 9;
				break;
			case 'v':
				value = 11;
				break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
				value = Integer.valueOf(val.substring(2, val.length() - 1), 8);
				break;
			case 'x':
				value = Integer.valueOf(val.substring(3, val.length() - 1), 16);
				break;
			default:
				throw new UnsupportedOperationException();
			}
		} else if (val.length() == 3)
			value = (int) val.charAt(1);
		else
			throw new UnsupportedOperationException();
		return String.valueOf(value);
	}

	/**
	 * Parses Integer constants according to <a
	 * href="www.open-std.org/jtc1/sc22/WG14/www/docs/n1256.pdf">ISO/IEC
	 * 9899:TC3</a>, chapter 6.4.4.2.
	 * 
	 * @param val
	 *            the value to parse
	 * @param loc
	 *            the location
	 * @return the parsed value
	 */
	public static final RValue handleFloatConstant(String val, ILocation loc,
			boolean bitvectorTranslation, 
			TypeSizes typeSizeConstants,
			FunctionDeclarations functionDeclarations) {
		if (bitvectorTranslation) {
			String value = val;
			String floatType = null;
			int exponentLength = 0;
			int significantLength = 0;
			int exponentValue = 0;
			final Expression sign = new BitvecLiteral(loc, Integer.toString(0), 1);
			final Expression significant;
			final Expression exponent;			
			

			// if there is a float-suffix: throw it away
			for (String s : SUFFIXES_FLOAT) {
				if (val.endsWith(s)) {
					value = val.substring(0, val.length() - s.length());
					floatType = s;
				}
			}
			BigDecimal floatVal = new BigDecimal(value);
			
			// Set floatIndices depending on the value of the val
			final CType resultType;
			if (floatType == null || floatType.equals("d") || floatType.equals("D")) {
				exponentLength = 11;
				significantLength = 53;
				resultType = new CPrimitive(CPrimitive.PRIMITIVE.DOUBLE);
			} else if (floatType.equals("f") || floatType.equals("F")) {
				exponentLength = 8;
				significantLength = 24;
				resultType = new CPrimitive(CPrimitive.PRIMITIVE.FLOAT);
			} else if (floatType.equals("l") || floatType.equals("L")) {
				exponentLength = 15;
				significantLength = 113;
				resultType = new CPrimitive(CPrimitive.PRIMITIVE.LONGDOUBLE);
			} else {
				throw new IllegalArgumentException("not a float type");
			}
			
			final Expression[] arguments;
			final String functionName;
			final IntegerLiteral eb = new IntegerLiteral(loc, Integer.toString(exponentLength));
			final IntegerLiteral sb = new IntegerLiteral(loc, Integer.toString(significantLength));
			if (value.equals("NAN") || value.equals("nan")) {
				functionName = "NaN";
				arguments = new Expression[]{eb, sb};
			} else if (value.equals("INFINITY")) {
				functionName = "+oo";
				arguments = new Expression[]{eb, sb};
			} else if (floatVal.compareTo(BigDecimal.ZERO) == 0) {
				functionName = "+zero";
				arguments = new Expression[] {eb, sb};
			} else {
				DeclarationInformation RoundingInfo = 
						new DeclarationInformation(StorageClass.GLOBAL, null);
				IdentifierExpression roundingMode = new IdentifierExpression(loc, "RNE");
				roundingMode.setDeclarationInformation(RoundingInfo);
				if (resultType.toString().equals("FLOAT")){
					functionName = "declareFloat";
				} else if (resultType.toString().equals("DOUBLE")) {
					functionName = "declareDouble";
				} else if (resultType.toString().equals("LONGDOUBLE")) {
					functionName = "declareLongDouble";
				} else {
					throw new IllegalArgumentException();
				}
				Expression realValue = new RealLiteral(loc, floatVal.toString());
				arguments = new Expression[] {eb, sb, roundingMode, realValue};
				/*
				final BigDecimal twoPointZero = new BigDecimal("2.0");
				// calculate exponent value and value of the significant
				while (floatVal.compareTo(twoPointZero) == 1) {
					floatVal = floatVal.divide(twoPointZero);
					exponentValue++;
				}
				String floatValString = floatVal.toString();
				if (floatValString.contains(".")) {
					floatValString = floatValString.substring(0, 1) + floatValString.substring(2, floatValString.length());
				}
				if (resultType.toString().equals("FLOAT")){
					functionName = "declareFloat";
				} else if (resultType.toString().equals("DOUBLE")) {
					functionName = "declareDouble";
				} else if (resultType.toString().equals("LONGDOUBLE")) {
					functionName = "declareLongDouble";
				} else {
					throw new IllegalArgumentException();
				}
				exponent = new BitvecLiteral(loc, Integer.toString(exponentValue), exponentLength);
				significant = new BitvecLiteral(loc, floatValString, significantLength);
				arguments = new Expression[]{sign, exponent, significant};
				*/
			}
			
			FunctionApplication func = new FunctionApplication(loc, SFO.AUXILIARY_FUNCTION_PREFIX + functionName, arguments);
			return new RValue(func, resultType);
			
		} else {
			String value = val;
			// if there is a float-suffix: throw it away
			for (String s : SUFFIXES_FLOAT) {
				if (val.endsWith(s)) {
					value = val.substring(0, val.length() - s.length());
					String msg = IGNORED_SUFFIX + " " + "Float suffix ignored: " + s;
					throw new UnsupportedSyntaxException(loc, msg);
				}
			}
			try {
				// check for integer-prefix.
				if (value.startsWith(HEX_L0X) || value.startsWith(HEX_U0X)) {
					// val is a hexadecimal-constant!
					//FIXME: --> is removing the + in front of the exponent enough??
					value = Double.valueOf(value.replaceAll("\\+", "")).toString();
				} else {
					Double.valueOf(value); //using double for good measure..
				}
				return new RValue(new RealLiteral(loc, value), new CPrimitive(PRIMITIVE.FLOAT));
			} catch (NumberFormatException nfe) {
				String msg = "Unable to translate float!";
				throw new IncorrectSyntaxException(loc, msg);
			}
		}
	}

	/**
	 * Parses Integer constants according to <a
	 * href="www.open-std.org/jtc1/sc22/WG14/www/docs/n1256.pdf">ISO/IEC
	 * 9899:TC3</a>, chapter 6.4.4.1.
	 * 
	 * @param valueWithSuffixes
	 *            the value to parse
	 * @param loc
	 *            the location
	 * @param bitvectorTranslation
	 *            if true the Expression of the resulting RValue is a bitvecor
	 *            if false the Expression is an int.
	 * @param typeSizeConstants
	 * 			  object that contains information about the size of
	 *  		  primitive types.
	 * @return the parsed value
	 */
	public static final RValue handleIntegerConstant(String valueWithPrefixAndSuffix, ILocation loc, 
			boolean bitvectorTranslation, 
			TypeSizes typeSizeConstants) {
		try {
			final IntegerConstant ic = new IntegerConstant(valueWithPrefixAndSuffix);
			final CPrimitive cType = determineCType(ic, typeSizeConstants);
			final Expression resultLiteral = constructLiteralForCIntegerLiteral(
					loc, bitvectorTranslation, typeSizeConstants, cType,
					ic.getValue());
			return new RValue(resultLiteral, cType);
		} catch (NumberFormatException nfe) {
			String msg = "Unable to translate int!";
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	public static Expression constructLiteralForCIntegerLiteral(
			ILocation loc, boolean bitvectorTranslation,
			TypeSizes typeSizeConstants, final CPrimitive cType,
			BigInteger value) {
		final Expression resultLiteral;
		if (bitvectorTranslation) {
			int bitlength = 8 * typeSizeConstants.getSize(cType.getType());
			if (value.signum() == -1) {
				long maxValue = (long) Math.pow(2, bitlength);
				value = value.add(BigInteger.valueOf(maxValue));
			}
			final BigInteger valueInRange = constructBitvectorInRange(value, bitlength);
			resultLiteral = new BitvecLiteral(loc, valueInRange.toString(), bitlength);
		} else {
			resultLiteral = new IntegerLiteral(loc, value.toString());
		}
		return resultLiteral;
	}
	
	/**
	 * @return the result of value % 2^bitlength
	 */
	public static BigInteger constructBitvectorInRange(BigInteger value, int bitlength) {
		return value.mod(new BigInteger("2").pow(bitlength));
	}
	
	private static class IntegerConstant {
		
		private final IntegerConstantType m_IntegerConstantType;
		private final String m_Suffix;
		private final BigInteger m_Value;
		public IntegerConstant(String valueWithPrefixAndSuffix) {
			String valueWithPrefix = valueWithPrefixAndSuffix;
			String suffix = "";
			for (String s : SUFFIXES_INT) {
				if (valueWithPrefixAndSuffix.endsWith(s)) {
					valueWithPrefix = valueWithPrefixAndSuffix.substring(0, valueWithPrefixAndSuffix.length() - s.length());
					suffix = s;
					break;
				}
			}
			m_Suffix = suffix;
			final String valueAsString;
			if (valueWithPrefix.startsWith(HEX_L0X) || valueWithPrefix.startsWith(HEX_U0X)) {
				// val is a hexadecimal-constant
				valueAsString = valueWithPrefix.substring(2);
				m_IntegerConstantType = IntegerConstantType.HEXADECIMAL;
			} else if (valueWithPrefix.startsWith(OCT_0)) {
				valueAsString = valueWithPrefix;
				m_IntegerConstantType = IntegerConstantType.OCTAL;
			} else {
				valueAsString = valueWithPrefix;
				m_IntegerConstantType = IntegerConstantType.DECIMAL;
			}
			m_Value = new BigInteger(valueAsString, m_IntegerConstantType.getBase());
		}
		
		public BigInteger getValue() {
			return m_Value;
		}
		public IntegerConstantType getIntegerConstantType() {
			return m_IntegerConstantType;
		}
		public boolean hasUnsignedSuffix() {
			return m_Suffix.contains("u") || m_Suffix.contains("U"); 
		}
		public boolean hasLongLongSuffix() {
			return m_Suffix.contains("ll") || m_Suffix.contains("LL"); 
		}
		public boolean hasLongSuffix() {
			return !hasLongLongSuffix() && (m_Suffix.contains("l") || m_Suffix.contains("L")); 
		}
	}
	
	/**
	 * Get the types that a given integer type can have.
	 * Returns the types in the correct order according to 6.4.4.1.5 of the 
	 * C11 standard.
	 */
	private static PRIMITIVE[] getPossibleTypes(IntegerConstant ic) {
		if (ic.hasUnsignedSuffix()) {
			if (ic.hasLongLongSuffix()) {
				return new PRIMITIVE[] { PRIMITIVE.ULONGLONG };
			} else if (ic.hasLongSuffix()) {
				return new PRIMITIVE[] { PRIMITIVE.ULONG, PRIMITIVE.ULONGLONG };
			} else {
				return new PRIMITIVE[] { PRIMITIVE.UINT, PRIMITIVE.ULONG, PRIMITIVE.ULONGLONG };
			}
		} else {
			if (ic.hasLongLongSuffix()) {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new PRIMITIVE[] { PRIMITIVE.LONGLONG };
				} else {
					return new PRIMITIVE[] { PRIMITIVE.LONGLONG, PRIMITIVE.ULONGLONG };
				}
			} else if (ic.hasLongSuffix()) {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new PRIMITIVE[] { PRIMITIVE.LONG, PRIMITIVE.LONGLONG };
				} else {
					return new PRIMITIVE[] { PRIMITIVE.LONG, PRIMITIVE.ULONG, PRIMITIVE.LONGLONG, PRIMITIVE.ULONGLONG };
				}
			} else {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new PRIMITIVE[] { PRIMITIVE.INT, PRIMITIVE.LONG, PRIMITIVE.LONGLONG };
				} else {
					return new PRIMITIVE[] { PRIMITIVE.INT, PRIMITIVE.UINT, PRIMITIVE.LONG, PRIMITIVE.ULONG, PRIMITIVE.LONGLONG, PRIMITIVE.ULONGLONG };
				}
			}
		}
	}
	
	private static CPrimitive determineCType(IntegerConstant ic, TypeSizes typeSizes) {
		PRIMITIVE[] primitives = getPossibleTypes(ic);
		for (PRIMITIVE primitive : primitives) {
			CPrimitive cPrimitive = new CPrimitive(primitive);
			BigInteger maxValue = typeSizes.getMaxValueOfPrimitiveType(cPrimitive);
			if (ic.getValue().compareTo(maxValue) <= 0) {
				return cPrimitive;
			}
		}
		throw new IllegalArgumentException("Unable to represent " + ic.getValue() 
			+ " using any of the given types. This is probably undefined"
			+ " or we need extended integer types. See 6.4.4.1 in the C standard");
	}
}
