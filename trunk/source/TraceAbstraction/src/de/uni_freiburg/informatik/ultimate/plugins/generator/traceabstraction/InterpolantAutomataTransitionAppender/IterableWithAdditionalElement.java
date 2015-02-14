package de.uni_freiburg.informatik.ultimate.plugins.generator.traceabstraction.InterpolantAutomataTransitionAppender;

import java.util.Iterator;
import java.util.NoSuchElementException;

/**
 * Extends an Iterable by an additional Object.
 * The additional Object is only returned in the iteration sequence if it occurs
 * not already in the iteration sequence (comparison via reference not equals!).
 * 
 * @author Matthias Heizmann
 *
 * @param <E>
 */
public class IterableWithAdditionalElement<E> implements Iterable<E> {

	private final Iterable<E> m_Iterable;
	private final E m_AdditionalElement;
	
	
	
	public IterableWithAdditionalElement(Iterable<E> iterable,
			E additionalElement) {
		super();
		m_Iterable = iterable;
		m_AdditionalElement = additionalElement;
	}



	@Override
	public Iterator<E> iterator() {
		
		return new Iterator<E>() {
			final Iterator<E> m_Iterator = m_Iterable.iterator();
			boolean m_AdditionalElementSeen = false;
			boolean m_AdditionalElementReturned = false;
			
			@Override
			public boolean hasNext() {
				if (m_Iterator.hasNext()) {
					return true;
				} else {
					if (m_AdditionalElementSeen) {
						return false;
					} else {
						return !m_AdditionalElementReturned;
					}
				}
			}

			@Override
			public E next() {
				if (m_Iterator.hasNext()) {
					E next = m_Iterator.next();
					if (next == m_AdditionalElement) {
						m_AdditionalElementSeen = true;
					}
					return next;
				} else {
					if (m_AdditionalElementSeen) {
						throw new NoSuchElementException();
					} else {
						if (m_AdditionalElementReturned) {
							throw new NoSuchElementException();
						} else {
							m_AdditionalElementReturned = true;
							return m_AdditionalElement;
						}
					}
				}
			}

			@Override
			public void remove() {
				throw new UnsupportedOperationException();
			}
		};
	}
	
}
