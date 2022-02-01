/* SimpleMap
 *
 * This file is part of the PEA tool set
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
 * $Id: SimpleMap.java 227 2006-10-19 07:29:43Z jfaber $
 */

package de.uni_freiburg.informatik.ultimate.lib.pea.util;
import java.util.AbstractMap;
import java.util.Map;
import java.util.Set;

/**
 * This is a very simple map, using a set as backing.  
 * The default backing set is a simple set, but you can specify any other
 * set of Map.Entry in the constructor.
 */
public class SimpleMap<Keys,Values> extends AbstractMap<Keys,Values> {
    private final Set<Entry<Keys,Values>> backing;

    public SimpleMap() {
	backing = new SimpleSet<Entry<Keys,Values>>();
    }
    
    public SimpleMap(int initialCapacity) {
	backing = new SimpleSet<Entry<Keys,Values>>(initialCapacity);
    }

    public SimpleMap(Set<Entry<Keys,Values>> fromSet) {
	backing = fromSet;
    }
	
    @Override
	public Set<Entry<Keys, Values>> entrySet() {
	return backing;
    }

    /**
     * SimpleEntry is a straight forward implemenation of
     * Map.Entry.
     *
     * @author hoenicke
     * @see java.util.Map.Enty
     */
    public static class SimpleEntry<K,V> implements Map.Entry<K,V> {
	K key;
	V value;

	public SimpleEntry(K key, V value) {
	    this.key = key;
	    this.value = value;
	}

	@Override
	public K getKey() {
	    return key;
	}

	@Override
	public V getValue() {
	    return value;
	}

	@Override
	public V setValue(V newValue) {
	    final V old = value;
	    value = newValue;
	    return old;
	}
	
	@Override
	public int hashCode() {
	    return key.hashCode() ^ value.hashCode();
	}

	@Override
	public boolean equals(Object o) {
	    if (o instanceof Entry) {
		final Entry e = (Entry) o;
		return key.equals(e.getKey()) && value.equals(e.getValue());
	    }
	    return false;
	}
    }

    @Override
	public Values put(Keys key, Values value) {
	for (final Entry<Keys,Values> entry: backing) {
	    if (key.equals(entry.getKey())) {
			return entry.setValue(value);
		}
	}
	backing.add(new SimpleEntry<Keys,Values>(key, value));
	return null;
    }
}
