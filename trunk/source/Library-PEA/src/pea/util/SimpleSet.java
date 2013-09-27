/* SimpleSet
 *
 * The PEA tool set is a collection of tools for 
 * Phase Event Automata (PEA). See
 * http://csd.informatik.uni-oldenburg.de/projects/peatools.html
 * for more information.
 * 
 * Copyright (C) 1999-2002 Jochen Hoenicke.
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
 * $Id: SimpleSet.java 227 2006-10-19 07:29:43Z jfaber $
 */

package pea.util;
import java.util.AbstractSet;
import java.util.Iterator;

public class SimpleSet<T> extends AbstractSet<T> implements Cloneable
{
    T[] elementObjects;
    int count = 0;

    public SimpleSet() {
	this(2);
    }

    @SuppressWarnings("unchecked")
    public SimpleSet(int initialSize) {
	elementObjects = (T[]) new Object[initialSize];
    }

    public int size() {
	return count;
    }

    @SuppressWarnings("unchecked")
    public boolean add(T element) {
	if (element == null)
	    throw new NullPointerException();

	for (int i=0; i< count; i++) {
	    if (element.equals(elementObjects[i]))
		return false;
	}
	
	if (count == elementObjects.length) {
            T[] newArray = (T[]) new Object[(count+1)*3/2];
            System.arraycopy(elementObjects,0,newArray,0,count);
            elementObjects = newArray;
        }
        elementObjects[count++] = element;
	return true;
    }
	
    @SuppressWarnings("unchecked")
    public Object clone() {
        try {
            SimpleSet<T> other = (SimpleSet<T>) super.clone();
	    other.elementObjects = (T[]) elementObjects.clone();
            return other;
        } catch (CloneNotSupportedException ex) {
            throw new InternalError("Clone?");
        }
    }

    public Iterator<T> iterator() {
	return new Iterator<T>() {
	    int pos = 0;

	    public boolean hasNext() {
		return pos < count;
	    }
	    
	    public T next() {
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
