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
/* SimpleSet Copyright (C) 1998-2002 Jochen Hoenicke.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation; either version 2, or (at your option)
 * any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with this program; see the file COPYING.LESSER.  If not, write to
 * the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.
 *
 * $Id: SimpleSet.java 1367 2002-05-29 12:06:47Z hoenicke $
 */

package de.uni_freiburg.informatik.ultimate.smtinterpol.convert;
import java.util.AbstractSet;
import java.util.Iterator;

public class SimpleSet<E> extends AbstractSet<E> implements Cloneable
{
	E[] elementObjects;
	int count = 0;

	public SimpleSet() {
		this(2);
	}

	@SuppressWarnings("unchecked")
	public SimpleSet(int initialSize) {
		elementObjects = (E[]) new Object[initialSize];
	}

	public int size() {
		return count;
	}

	@SuppressWarnings("unchecked")
	public boolean add(E element) {
		if (element == null)
			throw new NullPointerException();

		for (int i=0; i< count; i++) {
			if (element.equals(elementObjects[i]))
				return false;
		}
		
		if (count == elementObjects.length) {
			E[] newArray = (E[]) new Object[(count+1)*2];
			System.arraycopy(elementObjects,0,newArray,0,count);
			elementObjects = newArray;
		}
		elementObjects[count++] = element;
		return true;
	}
		
	@SuppressWarnings("unchecked")
	public Object clone() {
		try {
			SimpleSet<E> other = (SimpleSet<E>) super.clone();
			other.elementObjects = (E[]) elementObjects.clone();
			return other;
		} catch (CloneNotSupportedException ex) {
			throw new InternalError("Clone?");
		}
	}

	public Iterator<E> iterator() {
		return new Iterator<E>() {
			int pos = 0;

			public boolean hasNext() {
				return pos < count;
			}
			
			public E next() {
				return elementObjects[pos++];
			}
		  
			public void remove() {
				if (pos < count)
					System.arraycopy(elementObjects, pos, 
									 elementObjects, pos-1, count - pos);
				count--;
				pos--;
			}
		};
	}
}
