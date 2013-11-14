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

import java.io.IOException;
import java.util.ArrayDeque;

/**
 * This class converts a term into an Appendable (StringBuilder, 
 * OutputStreamWriter, etc).  It is non-recursive to prevent stack overflow. 
 * @author Jochen Hoenicke
 */
public class PrintTerm {
	/* This class iterates the term in a non-recursive way.  To achieve this
	 * it uses a todo stack, which contains terms and/or strings.
	 */
	private ArrayDeque<Object> m_Todo = new ArrayDeque<Object>();
	/**
	 * Convert a term into an appendable.
	 * @param appender The appendable.
	 * @param term     The term.
	 */
	public void append(Appendable appender, Term term) {
		try {
			m_Todo.push(term);
			run(appender);
		} catch (IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
	}
	/**
	 * Convert a sort into an appendable.  Note that sorts can get pretty long,
	 * too.  Hence we do this non-recursively to prevent stack overflows.
	 * @param appender The appendable.
	 * @param sort     The sort.
	 */
	public void append(Appendable appender, Sort sort) {
		try {
			m_Todo.push(sort);
			run(appender);
		} catch (IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
	}
	/**
	 * Append an s-expression.  The s-expression might contain terms.
	 * @param appender The appendable.
	 * @param sexpr    The s-expression.
	 */
	public void append(Appendable appender, Object[] sexpr) {
		try {
			m_Todo.push(sexpr);
			run(appender);
		} catch (IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
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
				return "|"+id+"|";
		}
		return id;
	}
	
	private void run(Appendable appender) throws IOException {
		while (!m_Todo.isEmpty()) {
			Object next = m_Todo.removeLast();
			if (next instanceof Term) {
				((Term)next).toStringHelper(m_Todo);
			} else if (next instanceof Sort) {
				((Sort)next).toStringHelper(m_Todo);
			} else if (next instanceof Object[]) {
				Object[] arr = (Object[]) next;
				m_Todo.addLast(")");
				for (int i = arr.length-1; i >= 0; i--) {
					m_Todo.addLast(arr[i]);
					if (i > 0)
						m_Todo.addLast(" ");
				}
				appender.append('(');
			} else {
				appender.append(next.toString());
			}
		}
	}
	
	public String toString() {
		return "[PrintTerm: " + m_Todo + "]";
	}
}
