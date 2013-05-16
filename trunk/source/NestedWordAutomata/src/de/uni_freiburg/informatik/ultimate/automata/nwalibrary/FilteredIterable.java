package de.uni_freiburg.informatik.ultimate.automata.nwalibrary;

import java.util.Iterator;
import java.util.Set;

public class FilteredIterable<T> implements Iterable<T> {
	Iterable<T> m_Iterable;
	Set<T> m_Filter;
	
	public FilteredIterable(Iterable<T> iterable, Set<T> filter) {
		m_Iterable = iterable;
		m_Filter = filter;
	}
	
	@Override
	public Iterator<T> iterator() {
		return new Iterator<T>() {
			final Iterator<T> m_Iterator;
			T m_next;
			{
				m_Iterator = m_Iterable.iterator();
				computeNext();
			}
			private void computeNext() {
				while (m_next != null && m_Iterator.hasNext() && !m_Filter.contains(m_next)) {
					m_next = m_Iterator.next();
				}
					
			}

			@Override
			public boolean hasNext() {
				return m_next != null;
			}

			@Override
			public T next() {
				T result = m_next;
				computeNext();
				return result;
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}

		};
	}

}
