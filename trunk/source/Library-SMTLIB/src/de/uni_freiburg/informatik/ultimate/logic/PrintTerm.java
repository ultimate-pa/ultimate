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
	protected final ArrayDeque<Object> mTodo = new ArrayDeque<>();
	/**
	 * Convert a term into an appendable.
	 * @param appender The appendable.
	 * @param term     The term.
	 */
	public void append(final Appendable appender, final Term term) {
		try {
			mTodo.add(term);
			run(appender);
		} catch (final IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
	}
	/**
	 * Convert a sort into an appendable.  Note that sorts can get pretty long,
	 * too.  Hence we do this non-recursively to prevent stack overflows.
	 * @param appender The appendable.
	 * @param sort     The sort.
	 */
	public void append(final Appendable appender, final Sort sort) {
		try {
			mTodo.add(sort);
			run(appender);
		} catch (final IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
	}

	/**
	 * Append an s-expression.  The s-expression might contain terms.
	 * @param appender The appendable.
	 * @param sexpr    The s-expression.
	 */
	public void append(final Appendable appender, final Object[] sexpr) {
		try {
			mTodo.add(sexpr);
			run(appender);
		} catch (final IOException ex) {
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
	public static String quoteIdentifier(final String id) {
		assert id.indexOf('|')  < 0 && id.indexOf('\\') < 0;
		for (int idx = 0; idx < id.length(); idx++) {
			final char c = id.charAt(idx);
			if (!(c >= 'A' && c <= 'Z')
				&& !(c >= 'a' && c <= 'z')
				&& !(c >= '0' && c <= '9' && idx > 0)
				&& "~!@$%^&*_+-=<>.?/".indexOf(c) < 0) {
				return "|" + id + "|";
			}
		}
		return id;
	}

	/**
	 * Ensure that object can be used as SMT-LIB 2 compliant identifier.
	 * otherwise the input is returned.
	 * @param value some object.
	 * @return quoted identifier if value is String, otherwise value
	 * (the input) is returned.
	 */
	public static Object quoteObjectIfString(final Object value) {
		if (value instanceof String) {
			final String valueAsString = String.valueOf(value);
			if (valueAsString.charAt(0) == '|' && valueAsString.charAt(valueAsString.length() - 1) == '|') {
				return value;
			} else {
				return quoteIdentifier(valueAsString);
			}
		} else {
			return value;
		}
	}

	/**
	 * Walk over a term and add its components to the todo queue.
	 *
	 * @param term the term.
	 */
	protected void walkTerm(final Term term) {
		term.toStringHelper(mTodo);
	}

	/**
	 * Walk over a sort and add its components to the todo queue.
	 *
	 * @param sort the sort.
	 */
	protected void walkSort(final Sort sort) {
		sort.toStringHelper(mTodo);
	}

	private void run(final Appendable appender) throws IOException {
		while (!mTodo.isEmpty()) {
			final Object next = mTodo.removeLast();
			if (next instanceof Term) {
				walkTerm((Term) next);
			} else if (next instanceof Sort) {
				walkSort((Sort) next);
			} else if (next instanceof Object[]) {
				final Object[] arr = (Object[]) next;
				mTodo.addLast(")");
				for (int i = arr.length - 1; i >= 0; i--) {
					mTodo.addLast(arr[i]);
					if (i > 0) {
						mTodo.addLast(" ");
					}
				}
				appender.append('(');
			} else {
				appender.append(next.toString());
			}
		}
	}

	@Override
	public String toString() {
		return "[PrintTerm: " + mTodo + "]";
	}
}
