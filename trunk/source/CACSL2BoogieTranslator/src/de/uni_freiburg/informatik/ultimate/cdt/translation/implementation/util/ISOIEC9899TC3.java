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
import java.util.ArrayList;
import java.util.List;
import java.util.function.Predicate;

import de.uni_freiburg.informatik.ultimate.boogie.ExpressionFactory;
import de.uni_freiburg.informatik.ultimate.boogie.ast.Expression;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler.TypeSizes;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.exception.IncorrectSyntaxException;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.result.RValue;
import de.uni_freiburg.informatik.ultimate.cdt.translation.interfaces.Dispatcher;
import de.uni_freiburg.informatik.ultimate.core.model.models.ILocation;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

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

		private final int mBase;

		IntegerConstantType(final int base) {
			mBase = base;
		}

		public int getBase() {
			return mBase;
		}
	}

	/**
	 * Parses Integer constants according to
	 * <a href="www.open-std.org/jtc1/sc22/WG14/www/docs/n1256.pdf">ISO/IEC
	 * 9899:TC3</a>, chapter 6.4.4.4.
	 *
	 * @param val
	 *            the value to parse
	 * @param loc
	 *            the location
	 * @return the parsed value
	 */
	public static BigInteger handleCharConstant(String val, final ILocation loc, final Dispatcher dispatch) {
		if (val.startsWith("L")) {
			// ignore wide character prefix
			val = val.substring(1, val.length());
			final String msg = IGNORED_SUFFIX + "Char-Sequence wide character suffix L dropped";
			dispatch.warn(loc, msg);
		}
		if (!val.startsWith("'") || !val.endsWith("'")) {
			throw new UnsupportedOperationException();
		}
		final String charSequence = val.substring(1, val.length() - 1);
		final Pair<BigInteger, String> pair = parseCharacterSequenceHelper(charSequence);
		final BigInteger value = pair.getFirst();
		final String remainingString = pair.getSecond();
		if (!remainingString.equals("")) {
			throw new UnsupportedOperationException(
					"integer character constants that consist of several characters are not yet supported.");
		}
		return value;
	}
	
	/**
	 * Takes as input a string from the source character set (characters that
	 * can occur in strings of source file, e.g., no line feed).
	 * Returns a sequence of numerical values of the corresponding characters
	 * of the execution character set. Multibyte characters occupy only one
	 * cell in the resulting list.
	 */
	public static List<BigInteger> parseCharacterSequence(final String sourceCharacterSequence) {
		final List<BigInteger> result = new ArrayList<>();
		String remainingString = sourceCharacterSequence;
		while (!remainingString.equals("")) {
			final Pair<BigInteger, String> pair = parseCharacterSequenceHelper(remainingString);
			result.add(pair.getFirst());
			remainingString = pair.getSecond();
		}
		return result;
	}

	/**
	 * Takes as input a string from the source character set (characters that
	 * can occur in strings of source file, e.g., no line feed). Returns a pair
	 * where the first element is the numerical value of the first character and
	 * the second element is the remaining string.
	 */
	private static Pair<BigInteger, String> parseCharacterSequenceHelper(final String sourceCharacterSequence) {
		final int numericalValue;
		final String remainingCharacterSequence;
		if (sourceCharacterSequence.charAt(0) != '\\') {
			numericalValue = sourceCharacterSequence.charAt(0);
			remainingCharacterSequence = sourceCharacterSequence.substring(1);
		} else {
			switch (sourceCharacterSequence.charAt(1)) {
			case '\'':
			case '\"':
			case '?':
			case '\\':
				numericalValue = sourceCharacterSequence.charAt(1);
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'a':
				numericalValue = 7;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'b':
				numericalValue = 8;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'f':
				numericalValue = 12;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'n':
				numericalValue = 10;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'r':
				numericalValue = 13;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 't':
				numericalValue = 9;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case 'v':
				numericalValue = 11;
				remainingCharacterSequence = sourceCharacterSequence.substring(2);
				break;
			case '0':
			case '1':
			case '2':
			case '3':
			case '4':
			case '5':
			case '6':
			case '7':
				final int lastSuccessiveOctalCharacter = lastsuccessiveMatchStartingFrom(1, sourceCharacterSequence,
						c -> isOctalDigit(c));
				// octal sequences consist only of up to three digits
				final int lastPositionOfThisOcalSequence;
				if (lastSuccessiveOctalCharacter >= 4) {
					lastPositionOfThisOcalSequence = 3;
				} else {
					lastPositionOfThisOcalSequence = lastSuccessiveOctalCharacter;
				}
				final String octalSequence = sourceCharacterSequence.substring(1, lastPositionOfThisOcalSequence + 1);
				numericalValue = Integer.valueOf(octalSequence, 8);
				remainingCharacterSequence = sourceCharacterSequence.substring(lastPositionOfThisOcalSequence + 1);
				break;
			case 'x':
				final int lastSuccessiveHexCharacter = lastsuccessiveMatchStartingFrom(2, sourceCharacterSequence,
						c -> isHexadecimalDigit(c));
				final String hexadecimalSequence = sourceCharacterSequence.substring(2, lastSuccessiveHexCharacter + 1);
				numericalValue = Integer.valueOf(hexadecimalSequence, 16);
				remainingCharacterSequence = sourceCharacterSequence.substring(lastSuccessiveHexCharacter + 1);
				break;
			default:
				throw new UnsupportedOperationException();
			}
		}
		return new Pair<BigInteger, String>(BigInteger.valueOf(numericalValue), remainingCharacterSequence);
	}
	
	
	/**
	 * Returns largest index i\>= startPost such all characters between 
	 * startPos and i (starPos and i included) satisfy the predicate p.
	 * Returns startpos-1 if the character at startPost does not satisfy p.
	 */
	static int lastsuccessiveMatchStartingFrom(final int startPos, final String str, final Predicate<Character> p) {
		for (int i=startPos; i<str.length(); i++) {
			if (!p.test(str.charAt(i))) {
				return i - 1;
			}
		}
		return str.length() - 1;
	}
	
	static boolean isOctalDigit(final char c) {
		switch (c) {
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
			return true;
		default:
			return false;
		}
	}
	
	static boolean isHexadecimalDigit(final char c) {
		switch (c) {
		case '0':
		case '1':
		case '2':
		case '3':
		case '4':
		case '5':
		case '6':
		case '7':
		case '8':
		case '9':
		case 'a':
		case 'A':
		case 'b':
		case 'B':
		case 'c':
		case 'C':
		case 'd':
		case 'D':
		case 'e':
		case 'E':
		case 'f':
		case 'F':
			return true;
		default:
			return false;
		}
	}
	
	/**
	 * Convert sequence of characters of the execution alphabet (given as a
	 * sequence of their numerical values) to a sequence of bytes. This step of
	 * the translation is largely implementation defined and we try to mimic the
	 * behavior of GCC.
	 */
	public static List<BigInteger> convertCharacterSequenceToByteSequence(final List<BigInteger> characterSequence,
			final Signedness signednessOfChar) {
		final List<BigInteger> result = new ArrayList<>();
		for (final BigInteger character : characterSequence) {
			BigInteger resultCharacter;
			if (character.compareTo(BigInteger.valueOf(255)) <= 0) {
				resultCharacter = convertNumericalValueToByteValue(signednessOfChar, character);
			} else {
				throw new UnsupportedOperationException("multibyte characters are not supported yet");
			}
			result.add(resultCharacter);
		}
		return result;
	}

	/**
	 * Although integer character constants have type 'int', C11 says in
	 * 6.4.4.4.10 that the values for single byte characters have to be in the
	 * value of 'char'. This means that (as explained in C11 6.4.4.4.13) if char
	 * is equivalent to unsigned char then \xFF has the value 255 and if char is
	 * equivalent to signed char then \xFF has the value -1. This methods
	 * implements a corresponding conversion.
	 */
	private static BigInteger convertNumericalValueToByteValue(final Signedness signednessOfChar,
			final BigInteger numericalValue) throws AssertionError {
		BigInteger byteValue;
		switch (signednessOfChar) {
		case SIGNED:
			if (numericalValue.compareTo(BigInteger.valueOf(127)) <= 0) {
				byteValue = numericalValue;
			} else {
				byteValue = numericalValue.subtract(BigInteger.valueOf(256));
			}
			break;
		case UNSIGNED:
			byteValue = numericalValue;
			break;
		default:
			throw new AssertionError("unknown value " + signednessOfChar);
		}
		return byteValue;
	}
	
	
	/**
	 * Parses FloatingPoint constants according to <a
	 * href="www.open-std.org/jtc1/sc22/WG14/www/docs/n1256.pdf">ISO/IEC
	 * 9899:TC3</a>, chapter 6.4.4.2.
	 *
	 * @param loc
	 *            the location
	 * @param val
	 *            the value to parse (as it occurs in the C program)
	 * @return Our representation of a floating point literal
	 */
	public static FloatingPointLiteral handleFloatConstant(final String value, final ILocation loc) {
		final String floatSuffix;
		String suffixFreeValue;
		{
			final Pair<String, String> pair = checkForFloatSuffix(value);
			suffixFreeValue = pair.getFirst();
			floatSuffix = pair.getSecond();
		}
		final BigDecimal resultValue = getDecimalForm(suffixFreeValue);
		final CPrimitive resultType = determineTypeFromSuffix(floatSuffix);
		final FloatingPointLiteral result = new FloatingPointLiteral(resultValue, resultType);
		return result;
	}

	/**
	 * Given a suffix-free decimal value, compute a BigDecimal representation of
	 * this value.
	 */
	private static BigDecimal getDecimalForm(final String suffixFreeValue) {
		final BigDecimal floatVal;
		// convert literal in hex form to decimal form
		if (suffixFreeValue.startsWith("0x") || suffixFreeValue.startsWith("0X")) {
			String hexValue = suffixFreeValue.substring(2);
			int suffixLength = -1;
			String hexExponentValue = null;

			// extract exponent value of the hex literal
			if (hexValue.contains("p")) {
				hexExponentValue = hexValue.substring(hexValue.indexOf('p') + 1);
				hexValue = hexValue.substring(0, hexValue.indexOf('p'));
			}

			if (hexValue.contains(".")) {
				final int dotPosition = hexValue.indexOf('.');
				suffixLength = hexValue.substring(dotPosition + 1).length();
				hexValue =
						hexValue.substring(0, dotPosition) + hexValue.substring(dotPosition + 1);
			}
			final BigInteger hexValueToDecimalValue = new BigInteger(hexValue, 16);
			BigDecimal hexValueBigDecimal = new BigDecimal(hexValueToDecimalValue.toString());

			if (hexExponentValue != null) {
				final int hexExponent = Integer.parseInt(hexExponentValue);
				if (hexExponent > 0) {
					for (int i = 0; i < hexExponent; i++) {
						hexValueBigDecimal = hexValueBigDecimal.multiply(new BigDecimal("2"));
					}
				} else if (hexExponent < 0) {
					for (int i = 0; i > hexExponent; i--) {
						hexValueBigDecimal = hexValueBigDecimal.divide(new BigDecimal("2"));
					}
				}
			}

			if (suffixLength != -1) {
				hexValueBigDecimal = hexValueBigDecimal.divide(BigDecimal.valueOf(Math.pow(16, suffixLength)));
			}
			floatVal = hexValueBigDecimal;
		} else if (suffixFreeValue.contains("e")) {
			// if value contains e calculate the number according to it
			final int eLocatation = suffixFreeValue.indexOf('e');
			final String floatString = suffixFreeValue.substring(0, eLocatation);
			final String exponentString = suffixFreeValue.substring(eLocatation + 1, suffixFreeValue.length());
			final BigDecimal base = new BigDecimal(floatString);
			final int exponent = Integer.parseInt(exponentString);
			floatVal = base.scaleByPowerOfTen(exponent);
		} else {
			floatVal = new BigDecimal(suffixFreeValue);
		}
		return floatVal;
	}

	/**
	 * Determine the type of a real floating type from the given float suffix.
	 *
	 * @param floatSuffix
	 *            either "d", "D", "f", "F", "l", "L"
	 */
	private static CPrimitive determineTypeFromSuffix(final String floatSuffix) {
		// Set floatIndices depending on the value of the val
		final CPrimitive resultType;
		if (floatSuffix == null || floatSuffix.equals("d") || floatSuffix.equals("D")) {
			resultType = new CPrimitive(CPrimitive.CPrimitives.DOUBLE);
		} else if (floatSuffix.equals("f") || floatSuffix.equals("F")) {
			resultType = new CPrimitive(CPrimitive.CPrimitives.FLOAT);
		} else if (floatSuffix.equals("l") || floatSuffix.equals("L")) {
			resultType = new CPrimitive(CPrimitive.CPrimitives.LONGDOUBLE);
		} else {
			throw new IllegalArgumentException("not a float type");
		}
		return resultType;
	}

	/**
	 * Check if value has float suffix.
	 * Return Pair whose first entry is a suffix-free float value and whose
	 * second entry is the float suffix. Use null as second if floatSuffix is
	 * null.
	 */
	private static Pair<String, String> checkForFloatSuffix(final String floatValue) {
		// if there is a float-suffix: throw it away
		for (final String s : SUFFIXES_FLOAT) {
			if (floatValue.endsWith(s)) {
				final String suffixFreeValue = floatValue.substring(0, floatValue.length() - s.length());
				final String floatSuffix = s;
				return new Pair<>(suffixFreeValue, floatSuffix);
			}
		}
		final String suffixFreeValue = floatValue;
		final String floatSuffix = null;
		return new Pair<>(suffixFreeValue, floatSuffix);
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
	 *            object that contains information about the size of
	 *            primitive types.
	 * @return the parsed value
	 */
	public static RValue handleIntegerConstant(final String valueWithPrefixAndSuffix, final ILocation loc,
			final boolean bitvectorTranslation,
			final TypeSizes typeSizeConstants) {
		try {
			final IntegerConstant ic = new IntegerConstant(valueWithPrefixAndSuffix);
			final CPrimitive cType = determineCType(ic, typeSizeConstants);
			final Expression resultLiteral = constructLiteralForCIntegerLiteral(
					loc, bitvectorTranslation, typeSizeConstants, cType,
					ic.getValue());
			return new RValue(resultLiteral, cType);
		} catch (final NumberFormatException nfe) {
			final String msg = "Unable to translate int! " + nfe.getMessage();
			throw new IncorrectSyntaxException(loc, msg);
		}
	}

	public static Expression constructLiteralForCIntegerLiteral(
			final ILocation loc, final boolean bitvectorTranslation,
			final TypeSizes typeSizeConstants, final CPrimitive cType,
			BigInteger value) {
		final Expression resultLiteral;
		if (bitvectorTranslation) {
			final int bitlength = 8 * typeSizeConstants.getSize(cType.getType());
			if (value.signum() == -1) {
				final long maxValue = (long) Math.pow(2, bitlength);
				value = value.add(BigInteger.valueOf(maxValue));
			}
			final BigInteger valueInRange = constructBitvectorInRange(value, bitlength);
			resultLiteral = ExpressionFactory.createBitvecLiteral(loc, valueInRange.toString(), bitlength);
		} else {
			resultLiteral = ExpressionFactory.createIntegerLiteral(loc, value.toString());
		}
		return resultLiteral;
	}

	/**
	 * @return the result of value % 2^bitlength
	 */
	public static BigInteger constructBitvectorInRange(final BigInteger value, final int bitlength) {
		return value.mod(new BigInteger("2").pow(bitlength));
	}

	private static class IntegerConstant {

		private final IntegerConstantType mIntegerConstantType;
		private final String mSuffix;
		private final BigInteger mValue;

		public IntegerConstant(final String valueWithPrefixAndSuffix) {
			String valueWithPrefix = valueWithPrefixAndSuffix;
			String suffix = "";
			for (final String s : SUFFIXES_INT) {
				if (valueWithPrefixAndSuffix.endsWith(s)) {
					valueWithPrefix =
							valueWithPrefixAndSuffix.substring(0, valueWithPrefixAndSuffix.length() - s.length());
					suffix = s;
					break;
				}
			}
			mSuffix = suffix;
			final String valueAsString;
			if (valueWithPrefix.startsWith(HEX_L0X) || valueWithPrefix.startsWith(HEX_U0X)) {
				// val is a hexadecimal-constant
				valueAsString = valueWithPrefix.substring(2);
				mIntegerConstantType = IntegerConstantType.HEXADECIMAL;
			} else if (valueWithPrefix.startsWith(OCT_0)) {
				valueAsString = valueWithPrefix;
				mIntegerConstantType = IntegerConstantType.OCTAL;
			} else {
				valueAsString = valueWithPrefix;
				mIntegerConstantType = IntegerConstantType.DECIMAL;
			}
			mValue = new BigInteger(valueAsString, mIntegerConstantType.getBase());
		}

		public BigInteger getValue() {
			return mValue;
		}

		public IntegerConstantType getIntegerConstantType() {
			return mIntegerConstantType;
		}

		public boolean hasUnsignedSuffix() {
			return mSuffix.contains("u") || mSuffix.contains("U");
		}

		public boolean hasLongLongSuffix() {
			return mSuffix.contains("ll") || mSuffix.contains("LL");
		}

		public boolean hasLongSuffix() {
			return !hasLongLongSuffix() && (mSuffix.contains("l") || mSuffix.contains("L"));
		}
	}

	/**
	 * Get the types that a given integer type can have.
	 * Returns the types in the correct order according to 6.4.4.1.5 of the
	 * C11 standard.
	 */
	private static CPrimitives[] getPossibleTypes(final IntegerConstant ic) {
		if (ic.hasUnsignedSuffix()) {
			if (ic.hasLongLongSuffix()) {
				return new CPrimitives[] { CPrimitives.ULONGLONG };
			} else if (ic.hasLongSuffix()) {
				return new CPrimitives[] { CPrimitives.ULONG, CPrimitives.ULONGLONG };
			} else {
				return new CPrimitives[] { CPrimitives.UINT, CPrimitives.ULONG, CPrimitives.ULONGLONG };
			}
		} else {
			if (ic.hasLongLongSuffix()) {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new CPrimitives[] { CPrimitives.LONGLONG };
				} else {
					return new CPrimitives[] { CPrimitives.LONGLONG, CPrimitives.ULONGLONG };
				}
			} else if (ic.hasLongSuffix()) {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new CPrimitives[] { CPrimitives.LONG, CPrimitives.LONGLONG };
				} else {
					return new CPrimitives[] { CPrimitives.LONG, CPrimitives.ULONG, CPrimitives.LONGLONG,
							CPrimitives.ULONGLONG };
				}
			} else {
				if (ic.getIntegerConstantType() == IntegerConstantType.DECIMAL) {
					return new CPrimitives[] { CPrimitives.INT, CPrimitives.LONG, CPrimitives.LONGLONG };
				} else {
					return new CPrimitives[] { CPrimitives.INT, CPrimitives.UINT, CPrimitives.LONG, CPrimitives.ULONG,
							CPrimitives.LONGLONG, CPrimitives.ULONGLONG };
				}
			}
		}
	}

	private static CPrimitive determineCType(final IntegerConstant ic, final TypeSizes typeSizes) {
		final CPrimitives[] primitives = getPossibleTypes(ic);
		for (final CPrimitives primitive : primitives) {
			final CPrimitive cPrimitive = new CPrimitive(primitive);
			final BigInteger maxValue = typeSizes.getMaxValueOfPrimitiveType(cPrimitive);
			if (ic.getValue().compareTo(maxValue) <= 0) {
				return cPrimitive;
			}
		}
		throw new IllegalArgumentException("Unable to represent " + ic.getValue()
				+ " using any of the given types. This is probably undefined"
				+ " or we need extended integer types. See 6.4.4.1 in the C standard");
	}

	public static class FloatingPointLiteral {
		private final BigDecimal mDecimalRepresenation;
		private final CPrimitive mCPrimitive;

		public FloatingPointLiteral(final BigDecimal decimalRepresenation, final CPrimitive cPrimitive) {
			super();
			mDecimalRepresenation = decimalRepresenation;
			mCPrimitive = cPrimitive;
		}

		public BigDecimal getDecimalRepresenation() {
			return mDecimalRepresenation;
		}

		public CPrimitive getCPrimitive() {
			return mCPrimitive;
		}

	}
}
