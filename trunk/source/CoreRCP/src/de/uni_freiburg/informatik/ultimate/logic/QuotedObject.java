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

public class QuotedObject {
	/**
	 * The underlying Object.
	 */
	private Object m_Obj;
	
	public QuotedObject(Object value) {
		m_Obj = value;
	}
	
	public Object getValue() {
		return m_Obj;
	}

	private static String quoteString(String str) {
		StringBuilder sb = new StringBuilder();
		sb.append('\"');
		for (int i = 0; i < str.length(); i++) {
			char c = str.charAt(i);
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

	public String toString() {
		return quoteString(m_Obj.toString());
	}
}
