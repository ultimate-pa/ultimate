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
import java.util.List;

import de.uni_freiburg.informatik.ultimate.cdt.translation.implementation.util.ISOIEC9899TC3;
import de.uni_freiburg.informatik.ultimate.plugins.generator.cacsl2boogietranslator.preferences.CACSLPreferenceInitializer.Signedness;

/**
 *
 *
 * @author Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 */
public class CStringLiteral {
	
	/**
	 * Input string from the source character set (characters that
	 * can occur in strings of source file, e.g., no line feed).
	 */
	private final String mSourceCharacterString;
	
	
	/**
	 * Sequence of numerical values of the corresponding characters
	 * of the execution character set. Multibyte characters occupy only one
	 * cell in the resulting list.
	 */
	private final List<BigInteger> mNumericalValues;
	
	
	/**
	 * Sequence of bytes that represent the string.  This step of
	 * the translation is largely implementation defined and we try to mimic the
	 * behavior of GCC.
	 */
	private final List<BigInteger> mByteValues;
	
	/**
	 * The Signedness of 'char' determines the representation of the string's
	 * characters when stored as a sequence of bytes.
	 */
	private final Signedness mSignednessOfChar;
	

	public CStringLiteral(final char[] quotedSourceCodeStringLiteral, final Signedness signednessOfChar) {
		mSourceCharacterString = stripQuotes(new String(quotedSourceCodeStringLiteral));
		mSignednessOfChar = signednessOfChar;
		mNumericalValues = ISOIEC9899TC3.parseCharacterSequence(mSourceCharacterString);
		// string literals are "nullterminated" i.e., suffixed by 0
		mNumericalValues.add(BigInteger.ZERO);
		mByteValues = ISOIEC9899TC3.convertCharacterSequenceToByteSequence(mNumericalValues, mSignednessOfChar);
	}


	private String stripQuotes(final String quotedSourceCodeStringLiteral) {
		String result;
		if (quotedSourceCodeStringLiteral.length() >= 2 && quotedSourceCodeStringLiteral.charAt(0) == '\"'
				&& quotedSourceCodeStringLiteral.charAt(quotedSourceCodeStringLiteral.length() - 1) == '\"') {
			result = quotedSourceCodeStringLiteral.substring(1, quotedSourceCodeStringLiteral.length() - 1);
		} else {
			throw new UnsupportedOperationException(
					"unsupported representation of string literal " + quotedSourceCodeStringLiteral);
		}
		return result;
	}


	public List<BigInteger> getByteValues() {
		return mByteValues;
	}
	
	
	
}
