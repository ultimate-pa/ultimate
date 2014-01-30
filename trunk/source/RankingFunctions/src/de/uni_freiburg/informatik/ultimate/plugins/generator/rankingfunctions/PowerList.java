package de.uni_freiburg.informatik.ultimate.plugins.generator.rankingfunctions;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.Iterator;
import java.util.List;
import java.util.NoSuchElementException;

/**
 * An iterator over the collection of all sublists of a list
 * 
 * @author Jan Leike
 *
 */
public class PowerList<E> implements Iterable<List<E>> {
	
	private List<E> m_base;
	
	public PowerList(List<E> base) {
		m_base = base;
	}
	
	@Override
	public Iterator<List<E>> iterator() {
		return new PowerListIterator();
	}
	
	class PowerListIterator implements Iterator<List<E>> {
		private int m_base_hash;
		
		private BitSet m_counter;
		private List<E> m_current;
		private boolean m_first = true;
		
		public PowerListIterator() {
			assert(m_base != null);
			m_base_hash = m_base.hashCode();
			m_current = new ArrayList<E>();
			m_counter = new BitSet(m_base.size() + 1);
		}
		
		/**
		 * Advance the iterator one step
		 */
		private void advance() {
			if (m_first) {
				m_first = false;
				return;
			}
			for (int i = 0; i <= m_base.size(); i++)  {
				if (!m_counter.get(i)) {
					m_counter.set(i);
					if (i < m_base.size()) {
						m_current.add(m_base.get(i));
					}
					break;
				} else {
					m_counter.clear(i);
					m_current.remove(m_base.get(i));
				}
			}
		}
		
		@Override
		public boolean hasNext() {
			return m_first || m_counter.cardinality() < m_base.size();
		}
		
		@Override
		public List<E> next() {
			assert(m_base.hashCode() == m_base_hash);
			if (!hasNext()) {
				throw new NoSuchElementException();
			}
			advance();
			return m_current;
		}
		
		@Override
		public void remove() {
			throw new UnsupportedOperationException();
		}
	}
}
