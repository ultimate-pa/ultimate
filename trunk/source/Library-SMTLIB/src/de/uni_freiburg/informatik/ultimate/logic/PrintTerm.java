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
	private final ArrayDeque<Object> mTodo = new ArrayDeque<Object>();
	/**
	 * Append an object to print.  This can be a term, a sort, 
	 * an Identifier (java type String), a number (BigInteger/BigDecimal),
	 * an s-expression (java type Object[]), a string (QuotedObject).
	 * @param appender The appendable.
	 * @param sexpr    The s-expression.
	 */
	public void append(Appendable appender, Object sexpr) {
		try {
			mTodo.push(sexpr);
			run(appender);
		} catch (IOException ex) {
			throw new RuntimeException("Appender throws IOException", ex);
		}
	}
	
	private void run(Appendable appender) throws IOException {
		while (!mTodo.isEmpty()) {
			Object next = mTodo.removeLast();
			if (next instanceof Term) {
				((Term)next).toStringHelper(mTodo);
			} else if (next instanceof Sort) {
				((Sort)next).toStringHelper(mTodo);
			} else if (next instanceof Object[]) {
				Object[] arr = (Object[]) next;
				mTodo.addLast(")");
				for (int i = arr.length - 1; i >= 0; i--) {
					mTodo.addLast(arr[i]);
					if (i > 0)
						mTodo.addLast(" ");
				}
				appender.append('(');
			} else {
				appender.append(next.toString());
			}
		}
	}
	
	public String toString() {
		return "[PrintTerm: " + mTodo + "]";
	}
}
