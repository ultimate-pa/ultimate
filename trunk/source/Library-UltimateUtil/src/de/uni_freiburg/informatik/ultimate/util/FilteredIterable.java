/*
 * Copyright (C) 2009-2015 University of Freiburg
 *
 * This file is part of the ULTIMATE Utils Library.
 *
 * The ULTIMATE Utils Library is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * The ULTIMATE Utils Library is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE Utils Library.  If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE Utils Library, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE Utils Library grant you additional permission 
 * to convey the resulting work.
 */
package de.uni_freiburg.informatik.ultimate.util;

import java.util.Iterator;

/**
 * Filter a given Iterable. Iterator returns only elements on which a given
 * predicate evaluates to true.
 * @author Matthias Heizmann
 *
 * @param <T>
 */
public class FilteredIterable<T> implements Iterable<T> {
	final Iterable<T> m_Iterable;
	final IPredicate<T> m_Predicate;
	
	public FilteredIterable(Iterable<T> iterable, IPredicate<T> remainingElements) {
		m_Iterable = iterable;
		m_Predicate = remainingElements;
	}
	
	@Override
	public Iterator<T> iterator() {
		return new Iterator<T>() {
			final Iterator<T> m_Iterator;
			T m_next = null;
			{
				m_Iterator = m_Iterable.iterator();
				if (m_Iterator.hasNext()) {
					getNextThatSatisfiesPredicate();
				}
			}
			private void getNextThatSatisfiesPredicate() {
				if (m_Iterator.hasNext()) {
					m_next = m_Iterator.next();
					while (m_next != null && !m_Predicate.evaluate(m_next)) {
						if (m_Iterator.hasNext()) {
							m_next = m_Iterator.next();
						} else {
							m_next = null;
						}
					}
				} else {
					m_next = null;
				}
			}

			@Override
			public boolean hasNext() {
				return m_next != null;
			}

			@Override
			public T next() {
				T result = m_next;
				getNextThatSatisfiesPredicate();
				return result;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}

		};
	}

}
