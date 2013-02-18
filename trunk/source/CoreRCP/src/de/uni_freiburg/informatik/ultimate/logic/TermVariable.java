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

import java.util.ArrayDeque;

public class TermVariable extends Term {
	private String m_Name;
	private Sort m_Sort;
	
	TermVariable(String n, Sort s, int hash) {
		super(hash);
		m_Name = n;
		m_Sort = s;
	}
	
	public String getName() {
		return m_Name;
	}

	public Sort getDeclaredSort() {
		return m_Sort;
	}
	
	public Sort getSort() {
		return m_Sort.getRealSort();
	}
	
	public String toString() {
		return PrintTerm.quoteIdentifier(m_Name);
	}

	public static final int hashVariable(String name, Sort sort) {
		return name.hashCode() ^ sort.hashCode();
	}

	@Override
	public void toStringHelper(ArrayDeque<Object> m_Todo) {
		m_Todo.add(toString());
	}
}
