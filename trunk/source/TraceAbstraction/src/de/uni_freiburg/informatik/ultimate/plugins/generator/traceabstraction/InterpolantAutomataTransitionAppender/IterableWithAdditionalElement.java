/*
 * Copyright (C) 2015 Matthias Heizmann (heizmann@informatik.uni-freiburg.de)
 * Copyright (C) 2015 University of Freiburg
 * 
 * This file is part of the ULTIMATE TraceAbstraction plug-in.
 * 
 * The ULTIMATE TraceAbstraction plug-in is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published
 * by the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 * 
 * The ULTIMATE TraceAbstraction plug-in is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU Lesser General Public License for more details.
 * 
 * You should have received a copy of the GNU Lesser General Public License
 * along with the ULTIMATE TraceAbstraction plug-in. If not, see <http://www.gnu.org/licenses/>.
 * 
 * Additional permission under GNU GPL version 3 section 7:
 * If you modify the ULTIMATE TraceAbstraction plug-in, or any covered work, by linking
 * or combining it with Eclipse RCP (or a modified version of Eclipse RCP), 
 * containing parts covered by the terms of the Eclipse Public License, the 
 * licensors of the ULTIMATE TraceAbstraction plug-in grant you additional permission 
 * to convey the resulting work.
 */
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
