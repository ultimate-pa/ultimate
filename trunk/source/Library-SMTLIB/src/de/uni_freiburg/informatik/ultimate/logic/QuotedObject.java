/*
 * Copyright (C) 2009-2012 University of Freiburg
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
 * A quoted object is used as value for string literals in SMTLIB 2.
 * The SMTLIB string literal
 * <pre>"..."</pre>
 * is represented by a ConstantTerm whose value is a quoted object.  The
 * underlying value is the string in parsed form, i.e., escape sequences using
 * backslash are removed and the surrounding quotes are removed.
 * 
 * A QuotedObject can also be used to quote arbitrary java objects.  These can
 * be used in annotations and will produce syntactically correct SMTLIB
 * scripts if they are dumped.
 * 
 * @author hoenicke
 */
public class QuotedObject {
	/**
	 * The underlying Object.
	 */
	private final Object mValue;

	/**
	 * Create a quoted object.
	 * @param value the value that is quoted.  Usually this is a string
	 * 	without the quotes.
	 */
	public QuotedObject(Object value) {
		mValue = value;
	}
	
	/**
	 * Get the underlying object.  
	 * @return the underlying object.
	 */
	public Object getValue() {
		return mValue;
	}

	private static String quoteString20(String str) {
		final StringBuilder sb = new StringBuilder();
		sb.append('\"');
		for (int i = 0; i < str.length(); i++) {
			final char c = str.charAt(i);
			switch(c) {
			case '\\':
				sb.append("\\\\");
				break;
			case '\"':
				sb.append("\\\"");
				break;
			default:
				sb.append(c);
				break;
			}
		}
		return sb.append('\"').toString();
	}
	
	private static String quoteString25(String str) {
		final StringBuilder sb = new StringBuilder();
		sb.append('\"');
		for (int i = 0; i < str.length(); i++) {
			final char c = str.charAt(i);
			if (c == '\"') {
				sb.append("\"\"");
			} else {
				sb.append(c);
			}
		}
		return sb.append('\"').toString();
	}

	/**
	 * Returns the SMTLIB 2.5 representation of the string.  This adds the
	 * quotes and converts escape sequences appropriately.
	 * @return the SMTLIB 2.5 compatible string representation.
	 */
	@Override
	public String toString() {
		return toString(true);
	}
	
	public String toString(boolean version25) {
		return version25 ? quoteString25(mValue.toString())
				: quoteString20(mValue.toString());
	}
}
