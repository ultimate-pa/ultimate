/*
 * Copyright (C) 2020 University of Freiburg
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
package de.uni_freiburg.informatik.ultimate.smtinterpol.smtlib2;

import java.util.Arrays;

import de.uni_freiburg.informatik.ultimate.smtinterpol.Config;

/**
 * Class to represent an S-expression.  An S-expression is represented internally as an array of objects.
 * The objects can be either arrays (sub-S-expressions), or other objects that implement a toString() method
 * to print their syntactical representation.
 * 
 * @author hoenicke
 *
 */
public class SExpression {
	private Object mData;

	public SExpression(Object data) {
		this.mData = data;
	}
	
	public Object getData() {
		return mData;
	}

	private static boolean convertSexp(final StringBuilder sb, Object sexpr, final int indentation) {
		if (sexpr instanceof Object[]) {
			sexpr = Arrays.asList((Object[]) sexpr);
		}
		if (sexpr instanceof Iterable) {
			if (Config.RESULTS_ONE_PER_LINE && indentation > 0) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < indentation; ++i) {
					sb.append(' ');
				}
			}
			sb.append('(');
			boolean subarray = false;
			String sep = "";
			for (final Object elem : (Iterable<?>) sexpr) {
				sb.append(sep);
				subarray |= convertSexp(sb, elem, indentation + Config.INDENTATION);
				sep = " ";
			}
			if (subarray && Config.RESULTS_ONE_PER_LINE) {
				sb.append(System.getProperty("line.separator"));
				for (int i = 0; i < indentation; ++i) {
					sb.append(' ');
				}
			}
			sb.append(')');
			return true;
		} else {
			sb.append(sexpr.toString());
		}
		return false;
	}

	/**
	 * Convert S-expression to its string representation.
	 */
	public String toString() {
		StringBuilder sb = new StringBuilder();
		convertSexp(sb, mData, 0);
		return sb.toString();
	}
}
