/*
 * Copyright (C) 2018 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
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
package de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.base.chandler;

import java.math.BigInteger;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.container.c.CPrimitive.CPrimitives;
import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;
import de.uni_freiburg.informatik.ultimate.util.datastructures.relation.Pair;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class CCharacterConstant {
	
	/**
	 * Representation of this character literal in source code. 
	 */
	private final String mSourceLiteral;
	
	
	private final BigInteger mNumericalValue;
	
	
	private final BigInteger mRepresentingValue;
	
	/**
	 * The signedness of 'char' determines the representation of the string's
	 * characters when stored as a sequence of bytes.
	 */
	private final Signedness mSignednessOfChar;
	
	private final Signedness mSignednessOfRepresentingType;
	
	private final CPrimitive mType;
	

	public CCharacterConstant(final String sourceLiteral, final Signedness signednessOfChar) {
		mSourceLiteral = sourceLiteral;
		mSignednessOfChar = signednessOfChar;
		String unquoted;
		switch (sourceLiteral.charAt(0)) {
		case '\'':
			// According to C11 6.4.4.4.10 the type of integer character
			// constants is int
			mType = new CPrimitive(CPrimitives.INT);
			mSignednessOfRepresentingType = Signedness.SIGNED;
			unquoted = sourceLiteral;
			break;
		case 'L':
			mType = new CPrimitive(CPrimitives.INT);
			mSignednessOfRepresentingType = Signedness.SIGNED;
			unquoted = sourceLiteral.substring(1);
			break;
		case 'u':
			mType = new CPrimitive(CPrimitives.USHORT);
			mSignednessOfRepresentingType = Signedness.UNSIGNED;
			unquoted = sourceLiteral.substring(1);
			break;
		case 'U':
			mType = new CPrimitive(CPrimitives.UINT);
			mSignednessOfRepresentingType = Signedness.UNSIGNED;
			unquoted = sourceLiteral.substring(1);
			break;
		default:
			throw new UnsupportedOperationException(sourceLiteral);
		}
		if (!unquoted.startsWith("'") || !unquoted.endsWith("'")) {
			throw new UnsupportedOperationException();
		}
		unquoted = unquoted.substring(1, unquoted.length() - 1);
		final Pair<BigInteger, String> pair = ISOIEC9899TC3.parseCharacterSequenceHelper(unquoted);
		mNumericalValue = pair.getFirst();
		final String remainingString = pair.getSecond();
		if (!remainingString.equals("")) {
			throw new UnsupportedOperationException(
					"integer character constants that consist of several characters are not yet supported.");
		}
		mRepresentingValue = computeRepresentingValue(mNumericalValue, signednessOfChar, mSignednessOfRepresentingType);
	}


	private BigInteger computeRepresentingValue(final BigInteger numericalValue, final Signedness signednessOfChar,
			final Signedness signednessOfRepresentingType) {
		BigInteger result;
		if (signednessOfChar == Signedness.SIGNED && signednessOfRepresentingType == Signedness.SIGNED) {
			if (numericalValue.compareTo(BigInteger.valueOf(255)) <= 0) {
				result = ISOIEC9899TC3.convertNumericalValueToByteValue(signednessOfChar, numericalValue);
			} else {
				throw new UnsupportedOperationException("multibyte characters are not supported yet");
			}
		} else {
			result = numericalValue;
		}
		return result;

	}


	public BigInteger getRepresentingValue() {
		return mRepresentingValue;
	}


	public CPrimitive getType() {
		return mType;
	}

	
	
	
}
