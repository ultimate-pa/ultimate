/*
 * Copyright (C) 2014 University of Freiburg
 *
 * This file is part of SMTInterpol.
 *
 * SMTInterpol is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * SMTInterpol is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with SMTInterpol.  If not, see <http://www.gnu.org/licenses/>.
 */
package de.uni_freiburg.informatik.ultimate.logic;

/**
 * An identifier is used in SExpressions to distinguish symbols that may
 * need to be quoted from other objects.  According to the SMTLIB2 standard
 * an identifier can contain arbitrary symbols except <code>|</code> and
 * <code>\</code>.  However, if it contains symbols outside 
 * <code>a...zA...Z0...9~!@$%^&amp;*_+-=&lt;&gt;.?/<code> or if it
 * starts with a digit it must be quoted in pipes.
 * 
 * @author hoenicke
 */
public class Identifier {
	/**
	 * The underlying symbol.
	 */
	private final String mIdentifier;

	/**
	 * Create an identifier.
	 * @param id the identifier without pipes.
	 */
	public Identifier(String id) {
		mIdentifier = id;
	}
	
	/**
	 * Get the underlying identifier.  
	 * @return the underlying identifier.
	 */
	public String getIdentifier() {
		return mIdentifier;
	}

	/**
	 * Ensure the identifier is SMTLIB 2 compliant.  If a symbol that is not
	 * allowed due to the SMTLIB 2 standard is encountered, the whole identifier
	 * will be quoted.
	 * @param id An unquoted identifier.
	 * @return SMTLIB 2 compliant identifier.
	 */
	public static String quoteIdentifier(String id) {
		assert id.indexOf('|')  < 0 && id.indexOf('\\') < 0;
		for (int idx = 0; idx < id.length(); idx++) {
			char c = id.charAt(idx);
			if (!(c >= 'A' && c <= 'Z')
				&& !(c >= 'a' && c <= 'z')
				&& !(c >= '0' && c <= '9' && idx > 0)
				&& "~!@$%^&*_+-=<>.?/".indexOf(c) < 0)
				return "|" + id + "|";
		}
		return id;
	}

	/**
	 * Returns the SMTLIB 2 representation of the string.  This adds the
	 * quotes and converts escape sequences appropriately.
	 * @return the SMTLIB 2 compatible string representation.
	 */
	public String toString() {
		return quoteIdentifier(mIdentifier);
	}
}
